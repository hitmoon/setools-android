#include <getopt.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
extern "C"
{
#define class _class
#define bool _bool
#include "sepol/policydb/policydb.h"
#include "sepol/policydb/services.h"
#include "sepol/policydb/expand.h"
#include "sepol/policydb/link.h"
#include "sepol/policydb/avrule_block.h"
#include "sepol/policydb/conditional.h"
#include "sepol/policydb/hashtab.h"

#undef class
#undef bool

	int policydb_index_decls(policydb_t *p);
	int avtab_remove(avtab_t * h, avtab_key_t * key);
}
#include "tktrace.h"
#include <dlfcn.h>

/* Error code
 * 1 => insert fail
 * 2 => Out of memory
 * 3 => set_attr error
 * 4 => policy_db error
 * 5 => source does not exist
 * 6 => target does not exist
 * 7 => class does not exist
 * 8 => perm does not exist
 * 9 => open policy file error
 * 10 => mmap policy file error
 * 11 => parse policy db error
 * 12 => open kernel policy error
 * 13 => write kernel policy error
 * 14 => set permissve bit error
 */

#define MAX_PERM 128
#define MAX_CMD  128

#define XATTR_NAME_SELINUX "security.selinux"

typedef int (*setxattr_ptr) (const char *, const char *, const void *, size_t, int);


struct rule_def {
	char *source;
	char *target;
	char *Class;
	char perm[MAX_PERM]; //strtok_r can not handle cosnt char *!!
};

static int set_attr(const char *type, policydb_t *policy, int value) {
	type_datum_t *attr = (type_datum_t *)hashtab_search(policy->p_types.table, (hashtab_key_t)type);
	if (!attr)
		return 3;
	if (ebitmap_set_bit(&attr->types, value - 1, 1))
		return 3;
	return 0;
}

int create_domain(const char *domain, policydb_t *policy) {
	uint32_t value = 0;
	type_datum_t datum, *type_datum;
	int r;
	unsigned int i;
	symtab_datum_t *src = (symtab_datum_t *)hashtab_search(policy->p_types.table, (hashtab_key_t)domain);
	if (src)
		return 0;

	type_datum = &datum;
	type_datum_init(type_datum);
	type_datum->primary = 1;
	type_datum->flavor = TYPE_TYPE;

	r = symtab_insert(policy, SYM_TYPES, strdup(domain), type_datum, SCOPE_DECL, 1, &value);
	type_datum->s.value = value;
	//fprintf(stderr, "source type %s does not exist: %d, %d\n", domain, r, value);
	if (ebitmap_set_bit(&policy->global->branch_list->declared.scope[SYM_TYPES], value - 1, 1)) {
		return 3;
	}

	policy->type_attr_map = (ebitmap_t *)realloc(policy->type_attr_map, sizeof(ebitmap_t) * policy->p_types.nprim);
	policy->attr_type_map = (ebitmap_t *)realloc(policy->attr_type_map, sizeof(ebitmap_t) * policy->p_types.nprim);
	ebitmap_init(&policy->type_attr_map[value - 1]);
	ebitmap_init(&policy->attr_type_map[value - 1]);
	ebitmap_set_bit(&policy->type_attr_map[value - 1], value - 1, 1);

	// Add the domain to all roles
	for (i = 0; i < policy->p_roles.nprim; i++) {
		// Not sure all those three calls are needed
		ebitmap_set_bit(&policy->role_val_to_struct[i]->types.negset,
				value - 1, 0);
		ebitmap_set_bit(&policy->role_val_to_struct[i]->types.types,
				value - 1, 1);
		type_set_expand(&policy->role_val_to_struct[i]->types,
				&policy->role_val_to_struct[i]->cache,
				policy, 0);
	}

	src = (symtab_datum *)hashtab_search(policy->p_types.table, (hashtab_key_t)domain);
	if (!src)
		return 1;

	if (policydb_index_decls(policy))
		return 4;
	if (policydb_index_classes(policy))
		return 4;
	if (policydb_index_others(NULL, policy, 1))
		return 4;
	return set_attr("domain", policy, value);
}

int mod_rule(int add, char *s, char *t, char *c, char *p, policydb_t *policy) {
	type_datum_t *src, *tgt;
	class_datum_t *cls;
	perm_datum_t *perm;
	avtab_datum_t *av;
	avtab_key_t key;

	src = (type_datum_t *)hashtab_search(policy->p_types.table, s);
	if (src == NULL) {
		//fprintf(stderr, "source type %s does not exist\n", s);
		return 5;
	}
	tgt = (type_datum_t *)hashtab_search(policy->p_types.table, t);
	if (tgt == NULL) {
		//fprintf(stderr, "target type %s does not exist\n", t);
		return 6;
	}
	cls = (class_datum *)hashtab_search(policy->p_classes.table, c);
	if (cls == NULL) {
		//fprintf(stderr, "class %s does not exist\n", c);
		return 7;
	}
	perm = (perm_datum *)hashtab_search(cls->permissions.table, p);
	if (perm == NULL) {
		if (cls->comdatum == NULL) {
			//fprintf(stderr, "perm %s does not exist in class %s\n", p, c);
			return 8;
		}
		perm = (perm_datum *)hashtab_search(cls->comdatum->permissions.table, p);
		if (perm == NULL) {
			//fprintf(stderr, "perm %s does not exist in class %s\n", p, c);
			return 8;
		}
	}

	// See if there is already a rule
	key.source_type = src->s.value;
	key.target_type = tgt->s.value;
	key.target_class = cls->s.value;
	key.specified = AVTAB_ALLOWED;
	av = avtab_search(&policy->te_avtab, &key);

	if (av == NULL && add) {
		av = (avtab_datum_t *) malloc(sizeof *av);
		if (av == NULL)
			return 2;
		av->data |= 1U << (perm->s.value - 1);
		int ret = avtab_insert(&policy->te_avtab, &key, av);
		if (ret) {
			//fprintf(stderr, "Error inserting into avtab\n");
			return 1;
		}
	} else if (av && add) {
		av->data |= 1U << (perm->s.value - 1);
	} else if (av && !add) {
		int ret = avtab_remove(&policy->te_avtab, &key);
		if (ret) {
			//fprintf(stderr, "Error removing from avtab\n");
			return 1;
		}
	}

	return 0;
}

int load_policy(const char *filename, policydb_t *policydb, struct policy_file *pf) {
	int fd;
	struct stat sb;
	void *map;
	int ret;

	fd = open(filename, O_RDONLY);
	if (fd < 0) {
		//fprintf(stderr, "Can't open '%s':  %s\n", filename, strerror(errno));
		return 9;
	}
	if (fstat(fd, &sb) < 0) {
		//fprintf(stderr, "Can't stat '%s':  %s\n", filename, strerror(errno));
		return 9;
	}
	map = mmap(NULL, sb.st_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
	if (map == MAP_FAILED) {
		//fprintf(stderr, "Can't mmap '%s':  %s\n", filename, strerror(errno));
		close(fd);
		return 10;
	}

	policy_file_init(pf);
	pf->type = PF_USE_MEMORY;
	pf->data = (char *)map;
	pf->len = sb.st_size;
	if (policydb_init(policydb)) {
		//fprintf(stderr, "policydb_init: Out of memory!\n");
		munmap(map, sb.st_size);
		close(fd);
		return 4;
	}
	ret = policydb_read(policydb, pf, 0);
	if (ret) {
		//fprintf(stderr, "error(s) encountered while parsing configuration\n");
		munmap(map, sb.st_size);
		close(fd);
		return 11;
	}

	munmap(map, sb.st_size);
	close(fd);
	return 0;
}

int load_policy_into_kernel(policydb_t *policydb) {
	const char *filename = "/sys/fs/selinux/load";
	int fd, ret;
	void *data = NULL;
	size_t len;

	policydb_to_image(NULL, policydb, &data, &len);

	// based on libselinux security_load_policy()
	fd = open(filename, O_RDWR);
	if (fd < 0) {
		//fprintf(stderr, "Can't open '%s':  %s\n", filename, strerror(errno));
		return 12;
	}
	ret = write(fd, data, len);
	close(fd);
	if (ret < 0) {
		//fprintf(stderr, "Could not write policy to %s\n", filename);
		return 13;
	}
	return 0;
}

int set_permissive(const char *domain, int permissive)
{
	policydb_t policydb;
	struct policy_file pf, outpf;
	type_datum_t *type;
	sidtab_t sidtab;
	int ret;
	const char *policy = "/sys/fs/selinux/policy";

	sepol_set_policydb(&policydb);
	sepol_set_sidtab(&sidtab);

	if ((ret = load_policy(policy, &policydb, &pf)) != 0) {
		//fprintf(stderr, "Could not load policy\n");
		return ret;
	}

	if (policydb_load_isids(&policydb, &sidtab))
		return 1;

	ret = create_domain(domain, &policydb);
	if (ret)
		return ret;
	type = (type_datum *)hashtab_search(policydb.p_types.table, (hashtab_key_t)domain);
	if (type == NULL) {
		//fprintf(stderr, "type %s does not exist\n", domain);
		return 5;
	}
	if (ebitmap_set_bit(&policydb.permissive_map, type->s.value, permissive)) {
		//fprintf(stderr, "Could not %s bit in permissive map\n", permissive ? "set" : "clear");
		return 14;
	}
	if ((ret = load_policy_into_kernel(&policydb)) != 0) {
		//fprintf(stderr, "Could not load new policy into kernel\n");
		return ret;
	}

	policydb_destroy(&policydb);

	return 0;

}

static int get_cmd(char *dest)
{
	const char *path = "/proc/self/cmdline";

	FILE *fp;

	fp = fopen(path, "r");
	if (fp == NULL)
		return -1;

	fgets(dest, MAX_CMD, fp);
	fclose(fp);

	return 0;
}

static int add_rules(struct rule_def *rules, int num) {
	int i, ret;
	policydb_t policydb;
	struct policy_file pf;
	sidtab_t sidtab;
	char *perm_token, *perm_saveptr = NULL;

	const char *policy = "/sys/fs/selinux/policy";

	sepol_set_policydb(&policydb);
	sepol_set_sidtab(&sidtab);

	if ((ret = load_policy(policy, &policydb, &pf)) != 0) {
		//fprintf(stderr, "Could not load policy\n");
		return ret;
	}

	if (policydb_load_isids(&policydb, &sidtab))
		return 1;

	for (i = 0; i < num; i++) {

		perm_token = strtok_r(rules[i].perm, ",", &perm_saveptr);
		if (perm_token)
			ret = create_domain(rules[i].source, &policydb);
		if (ret)
			return ret;
		while (perm_token) {
			/* add rule */
			if ((ret = mod_rule(1, rules[i].source, rules[i].target, rules[i].Class, perm_token, &policydb)) != 0) {
				//fprintf(stderr, "Could not add rule for perm: %s\n", perm_token);
				return ret;
			}

			perm_token = strtok_r(NULL, ",", &perm_saveptr);
		}
	}
	if ((ret = load_policy_into_kernel(&policydb)) != 0) {
		//fprintf(stderr, "Could not load new policy into kernel\n");
		return ret;
	}
	policydb_destroy(&policydb);

	return 0;
}

static int android_version_ge_5()
{
	const char *prop_path = "/system/build.prop";
	char key[128];
	char value[128];
        char line[256];
	FILE *fp = fopen(prop_path, "r");
        char *pos;

	if (fp == NULL) {
		return -1;
	}
	while (fgets(line, 256, fp)) {
                if (line[0] == '#')
                        continue;

                pos = strchr(line, '=');
                if (!pos)
                        continue;
                strncpy(key, line, pos - line);
                key[pos - line] = '\0';
                strcpy(value, pos + 1);
		if (strcmp(key, "ro.build.version.sdk") == 0) {
			if (atoi(value) >= 21)
				goto yes;
			goto no;
		}
		if (strcmp(key, "ro.build.version.release") == 0) {
			if (value[0] >= '5')
				goto yes;
			goto no;
		}
	}

	fclose(fp);
	return -1;

yes:
	fclose(fp);
	return 1;
no:
	fclose(fp);
	return 0;
}


int set_enforce(int value)
{
	int fd, ret;
	char path[PATH_MAX];
	char buf[20];

	snprintf(path, sizeof path, "/sys/fs/selinux/enforce");
	fd = open(path, O_RDWR);
	if (fd < 0)
		return -1;

	snprintf(buf, sizeof buf, "%d", value);
	ret = write(fd, buf, strlen(buf));
	close(fd);
	if (ret < 0)
		return -1;

	return 0;
}

int set_file_con(const char *path, const char *label)
{
	void *handle;
	int ret = -1;
	setxattr_ptr setxattr;

	if ((handle = dlopen("/system/lib/libc.so", RTLD_NOW)) == NULL) {
		return -1;
	}
	setxattr = (setxattr_ptr)dlsym(handle, "lsetxattr");

	if (setxattr) {
		ret =  setxattr(path, XATTR_NAME_SELINUX, label, strlen(label) + 1, 0);
	}
	dlclose(handle);
	return ret;

}

int modify_sepolicy(void) {

	int ret;
	char cmd[MAX_CMD];

	ret = get_cmd(cmd);
	if (!(strstr(cmd, "debuggerd") || strstr(cmd, "vold") || strstr(cmd, "netd")))
	    return 0;

	/* only work above android 5.0 */
	if (android_version_ge_5() == 0)
		goto done;

	ret = set_permissive("init", 1);
done:
	set_enforce(0);

	return ret;
}
