/* 
 * This was derived from public domain works with updates to 
 * work with more modern SELinux libraries. 
 * 
 * It is released into the public domain.
 * 
 */

#include <getopt.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <sepol/policydb/policydb.h>
#include <sepol/policydb/services.h>

void usage(char *arg0) {
	fprintf(stderr, "%s -s <source type> -t <target type> -c <class> -p <perm>[,<perm2>,<perm3>,...] [-P <policy file>] [-o <output file>] [-l|--load]\n", arg0);
	fprintf(stderr, "%s -Z permissive_type [-P <policy file>] [-o <output file>] [-l|--load]\n", arg0);
	fprintf(stderr, "%s -z permissive_type [-P <policy file>] [-o <output file>] [-l|--load]\n", arg0);
	exit(1);
}

void *cmalloc(size_t s) {
	void *t = malloc(s);
	if (t == NULL) {
		fprintf(stderr, "Out of memory\n");
		exit(1);
	}
	return t;
}

int add_rule(char *s, char *t, char *c, char *p, policydb_t *policy) {
	type_datum_t *src, *tgt;
	class_datum_t *cls;
	perm_datum_t *perm;
	avtab_datum_t *av;
	avtab_key_t key;

	src = hashtab_search(policy->p_types.table, s);
	if (src == NULL) {
		fprintf(stderr, "source type %s does not exist\n", s);
		return 2;
	}
	tgt = hashtab_search(policy->p_types.table, t);
	if (tgt == NULL) {
		fprintf(stderr, "target type %s does not exist\n", t);
		return 2;
	}
	cls = hashtab_search(policy->p_classes.table, c);
	if (cls == NULL) {
		fprintf(stderr, "class %s does not exist\n", c);
		return 2;
	}
	perm = hashtab_search(cls->permissions.table, p);
	if (perm == NULL) {
		if (cls->comdatum == NULL) {
			fprintf(stderr, "perm %s does not exist in class %s\n", p, c);
			return 2;
		}
		perm = hashtab_search(cls->comdatum->permissions.table, p);
		if (perm == NULL) {
			fprintf(stderr, "perm %s does not exist in class %s\n", p, c);
			return 2;
		}
	}

	// See if there is already a rule
	key.source_type = src->s.value;
	key.target_type = tgt->s.value;
	key.target_class = cls->s.value;
	key.specified = AVTAB_ALLOWED;
	av = avtab_search(&policy->te_avtab, &key);

	if (av == NULL) {
		av = cmalloc(sizeof av);
		av->data |= 1U << (perm->s.value - 1);
		int ret = avtab_insert(&policy->te_avtab, &key, av);
		if (ret) {
			fprintf(stderr, "Error inserting into avtab\n");
			return 1;
		}	
	}

	av->data |= 1U << (perm->s.value - 1);

	return 0;
}

int load_policy(char *filename, policydb_t *policydb, struct policy_file *pf) {
	int fd;
	struct stat sb;
	void *map;
	int ret;

	fd = open(filename, O_RDONLY);
	if (fd < 0) {
		fprintf(stderr, "Can't open '%s':  %s\n",
		        filename, strerror(errno));
		return 1;
	}
	if (fstat(fd, &sb) < 0) {
		fprintf(stderr, "Can't stat '%s':  %s\n",
		        filename, strerror(errno));
		return 1;
	}
	map = mmap(NULL, sb.st_size, PROT_READ | PROT_WRITE, MAP_PRIVATE,
	           fd, 0);
	if (map == MAP_FAILED) {
		fprintf(stderr, "Can't mmap '%s':  %s\n",
		        filename, strerror(errno));
		close(fd);
		return 1;
	}

	policy_file_init(pf);
	pf->type = PF_USE_MEMORY;
	pf->data = map;
	pf->len = sb.st_size;
	if (policydb_init(policydb)) {
		fprintf(stderr, "policydb_init: Out of memory!\n");
		munmap(map, sb.st_size);
		close(fd);
		return 1;
	}
	ret = policydb_read(policydb, pf, 1);
	if (ret) {
		fprintf(stderr, "error(s) encountered while parsing configuration\n");
		munmap(map, sb.st_size);
		close(fd);
		return 1;
	}

	munmap(map, sb.st_size);
	close(fd);
	return 0;
}

int load_policy_into_kernel(policydb_t *policydb) {
	char *filename = "/sys/fs/selinux/load";
	int fd, ret;
	void *data = NULL;
	size_t len;

	policydb_to_image(NULL, policydb, &data, &len);

	// based on libselinux security_load_policy()
	fd = open(filename, O_RDWR);
	if (fd < 0) {
		fprintf(stderr, "Can't open '%s':  %s\n",
		        filename, strerror(errno));
		return 1;
	}
	ret = write(fd, data, len);
	close(fd);
	if (ret < 0) {
		fprintf(stderr, "Could not write policy to %s\n",
		        filename);
		return 1;
	}
	return 0;
}

int main(int argc, char **argv) {
	char *policy = NULL, *source = NULL, *target = NULL, *class = NULL, *perm = NULL, *perm_token = NULL, *perm_saveptr = NULL, *outfile = NULL, *permissive = NULL;
	policydb_t policydb;
	struct policy_file pf, outpf;
	sidtab_t sidtab;
	int ch;
	int ret_add_rule;
	int load = 0;
	FILE *fp;
	int is_permissive = 0;

	struct option long_options[] = {
		{"source", required_argument, NULL, 's'},
		{"target", required_argument, NULL, 't'},
		{"class", required_argument, NULL, 'c'},
		{"perm", required_argument, NULL, 'p'},
		{"policy", required_argument, NULL, 'P'},
		{"output", required_argument, NULL, 'o'},
		{"permissive", required_argument, NULL, 'Z'},
		{"not-permissive", required_argument, NULL, 'z'},
		{"load", no_argument, NULL, 'l'},
		{NULL, 0, NULL, 0}
	};

	while ((ch = getopt_long(argc, argv, "s:t:c:p:P:o:Z:z:l", long_options, NULL)) != -1) {
		switch (ch) {
		case 's':
			source = optarg;
			break;
		case 't':
			target = optarg;
			break;
		case 'c':
			class = optarg;
			break;
		case 'p':
			perm = optarg;
			break;
		case 'P':
			policy = optarg;
			break;
		case 'o':
			outfile = optarg;
			break;
		case 'Z':
			permissive = optarg;
			is_permissive = 1;
			break;
                case 'z':
			permissive = optarg;
			is_permissive = 0;
			break;
		case 'l':
			load = 1;
			break;
		default:
			usage(argv[0]);
		}
	}

	if ((!source || !target || !class || !perm) && !permissive)
		usage(argv[0]);

	if (!policy)
		policy = "/sys/fs/selinux/policy";

	sepol_set_policydb(&policydb);
	sepol_set_sidtab(&sidtab);

	if (load_policy(policy, &policydb, &pf)) {
		fprintf(stderr, "Could not load policy\n");
		return 1;
	}

	if (policydb_load_isids(&policydb, &sidtab))
		return 1;

	if (permissive) {
		type_datum_t *type;
		type = hashtab_search(policydb.p_types.table, permissive);
		if (type == NULL) {
			fprintf(stderr, "type %s does not exist\n", permissive);
			return 2;
		}
		if (ebitmap_set_bit(&policydb.permissive_map, type->s.value, is_permissive)) {
			fprintf(stderr, "Could not %s bit in permissive map\n", is_permissive ? "set" : "clear");
			return 1;
		}
	} else {
		perm_token = strtok_r(perm, ",", &perm_saveptr);
		while (perm_token) {
			if (ret_add_rule = add_rule(source, target, class, perm_token, &policydb)) {
				fprintf(stderr, "Could not add rule for perm: %s\n", perm_token);
				return ret_add_rule;
			}
			perm_token = strtok_r(NULL, ",", &perm_saveptr);
		}
	}

	if (outfile) {
		fp = fopen(outfile, "w");
		if (!fp) {
			fprintf(stderr, "Could not open outfile\n");
			return 1;
		}

		policy_file_init(&outpf);
		outpf.type = PF_USE_STDIO;
		outpf.fp = fp;

		if (policydb_write(&policydb, &outpf)) {
			fprintf(stderr, "Could not write policy\n");
			return 1;
		}

		fclose(fp);
	}

	if (load) {
		if (load_policy_into_kernel(&policydb)) {
			fprintf(stderr, "Could not load new policy into kernel\n");
			return 1;
		}
	}

	policydb_destroy(&policydb);

	fprintf(stdout, "Success\n");
	return 0;
}
