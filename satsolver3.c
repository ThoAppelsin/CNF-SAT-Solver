#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

#define BUFFERSIZE 1024
#define EXPLPC 4

typedef uint32_t bitstore;

#define sbitstore      (8 * sizeof(bitstore))
#define bit(x)         (1U << (x))
#define mask(x, y)     ((x) & bit(y))
#define is_s_set(s, i) mask((s)[(i) / sbitstore], (i) % sbitstore)
#define s_set(s, i)    (s)[(i) / sbitstore] |= bit((i) % sbitstore)

size_t n_clauses;
size_t n_vars;
bitstore ** clauses;
bitstore ** occurlists;

int n_lits;
float mean_occ_len;

size_t cconf_len;
size_t olconf_len;
size_t cfg_len;
size_t cfg_size;

// https://stackoverflow.com/a/109025/2736228
int count_bits(uint32_t i)
{
	i = i - ((i >> 1) & 0x55555555);
	i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
	return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

void init_globals(void) {
	cconf_len = n_clauses / sbitstore + 1;
	olconf_len = n_vars / sbitstore + 1;
	cfg_len = cconf_len + 2 * olconf_len;
	cfg_size = cfg_len * sizeof(bitstore);
}

void init_formula(void)
{
	init_globals();

	clauses = malloc((2 * n_clauses + 1) * sizeof * clauses);
	clauses += n_clauses;
	clauses[0] = NULL;

	occurlists = malloc((2 * n_vars + 1) * sizeof * occurlists);
	occurlists += n_vars;
	occurlists[0] = NULL;

	for (int i = 1; i <= n_clauses; i++) {
		clauses[i] = calloc(olconf_len, sizeof * clauses[i]);
		clauses[-i] = calloc(olconf_len, sizeof * clauses[i]);
	}

	for (int i = 1; i <= n_vars; i++) {
		occurlists[i] = calloc(cconf_len, sizeof * occurlists[i]);
		occurlists[-i] = calloc(cconf_len, sizeof * occurlists[-i]);
	}
}

void clean_formula(void)
{
	for (int i = 1; i <= n_clauses; i++) {
		free(clauses[i]);
		free(clauses[-i]);
	}

	for (int i = 1; i <= n_vars; i++) {
		free(occurlists[i]);
		free(occurlists[-i]);
	}

	free(clauses - n_clauses);
	free(occurlists - n_vars);
}

void lits_add(int lit, int i_clause)
{
	if (lit > 0) s_set(clauses[i_clause], lit);
	else         s_set(clauses[-i_clause], -lit);
	s_set(occurlists[lit], i_clause);
	n_lits++;
}

int read(FILE * fp)
{
	char buffer[BUFFERSIZE];

	while (fgets(buffer, BUFFERSIZE, fp) != NULL)
	switch (*buffer) {
		case 'c': // a comment
			break;
		case 'p': // the spec
			if (sscanf(buffer, "p cnf %u %u", &n_vars, &n_clauses) != 2) {
				fputs("Error at the spec line.\n", stderr);
				return 0;
			}
			goto spec_read;
		default:
			fputs("Spec line missing, malformed file.\n", stderr);
			return 0;
	}
spec_read:

	init_formula();

	int i_clause = 0;
	while (i_clause < n_clauses && fgets(buffer, BUFFERSIZE, fp) != NULL) {
		if (*buffer == 'c') { /* a comment */ }
		else { // a clause
			int lit;
			char * token = strtok(buffer, " ");
			i_clause++;

			while (token != NULL) {
				lit = atoi(token);
				if (lit == 0) break;

				lits_add(lit, i_clause);
				token = strtok(NULL, " ");
			}
		}
	}
	mean_occ_len = (float) n_lits / n_vars;

	if (i_clause != n_clauses) {
		fprintf(stderr, "%u/%u clauses are missing.\n", n_clauses - i_clause, n_clauses);
		return 0;
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		return 0;
	}

	return 1;
}

void lit_propagate(bitstore * cconf, int lit)
{
	bitstore * occurlist = occurlists[lit];
	for (int i = 0; i < cconf_len; i++)
		cconf[i] |= occurlist[i];
}

void var_assign(bitstore * config, int var, int ispos)
{
	bitstore * cconf = config;
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	bitstore * xconf;
	int lit;

	if (ispos) xconf = pconf, lit = var;
	else       xconf = nconf, lit = -var;
	
	s_set(xconf, var);
	lit_propagate(cconf, lit);
}

void lit_assign(bitstore * config, int lit)
{
	bitstore * cconf = config;
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	bitstore * xconf;
	int var;

	if (lit > 0) xconf = pconf, var = lit;
	else         xconf = nconf, var = -lit;

	s_set(xconf, var);
	lit_propagate(cconf, lit);
}

int clause_length(bitstore * config, int clause_i)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;
	bitstore * pclause = clauses[clause_i];
	bitstore * nclause = clauses[-clause_i];

	int c = 0;
	for (int i = 0; i < olconf_len; i++) {
		c += count_bits(pclause[i] & ~nconf[i]);
		c += count_bits(nclause[i] & ~pconf[i]);
	}

	return c;
}

// https://stackoverflow.com/a/757266/2736228
uint8_t least_bit_pos(uint32_t v)
{
	static const uint8_t debruijnbitposition2[32] = {
		0, 1, 28, 2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4, 8,
		31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9
	};
	return debruijnbitposition2[((uint32_t)((v & (-v)) * 0x077cb531u)) >> 27];
}

int get_unit(bitstore * config, int clause_i)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;
	bitstore * pclause = clauses[clause_i];
	bitstore * nclause = clauses[-clause_i];
	
	bitstore temp;
	for (int i = 0; i < olconf_len; i++) {
		temp = nclause[i] & ~pconf[i];
		if (temp) return -(least_bit_pos(temp) + i * sbitstore);

		temp = pclause[i] & ~nconf[i];
		if (temp) return least_bit_pos(temp) + i * sbitstore;
	}

	return 0;
}

int c_len_reductions(bitstore * config)
{
	bitstore * cconf = config;

	int last_edit = n_clauses + 1;

	for (int i = 1; i != last_edit; i++) {
		if (i == n_clauses + 1) i = 1;
		// is_s_set of cconf at i, signifies that the clause i is satisfied
		if (is_s_set(cconf, i)) continue;

		switch (clause_length(config, i)) {
			case 0: return 0;
			case 1:
				lit_assign(config, get_unit(config, i));
				last_edit = (i == 1) ? (n_clauses + 1) : i;
		}
	}

	return 1;
}

unsigned int e_occurrence_unsat(bitstore * cconf, int lit)
{
	bitstore * occurlist = occurlists[lit];
	for (int i = 0; i < cconf_len; i++)
		if (occurlist[i] & ~cconf[i])
			// 1111 0000 occurrences
			// 0011 1100 satisfied clauses
			// 1100 0011 ~satisfied clauses
			// 1100 0000 occurrences unsatisfied
			return 1U;
	return 0U;
}

unsigned int var_state(bitstore * cconf, int var)
{
	return e_occurrence_unsat(cconf, -var) << 1 | e_occurrence_unsat(cconf, var);
}

unsigned int ass_state(bitstore * nconf, bitstore * pconf, int var)
{
	return !!is_s_set(nconf, var) << 1 | !!is_s_set(pconf, var);
}

void purity_reduction(bitstore * config)
{
	bitstore * cconf = config;
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int last_edit = n_vars + 1;

	for (int i = 1; i != last_edit; i++) {
		if (i == n_vars + 1) i = 1;

		// skip the variables already set True/False
		if (is_s_set(pconf, i) || is_s_set(nconf, i)) continue;

		switch (var_state(cconf, i)) {
			case 0b01:
				var_assign(config, i, 1);
				last_edit = (i == 1) ? (n_vars + 1) : i;
				break;
			case 0b10:
				var_assign(config, i, 0);
				last_edit = (i == 1) ? (n_vars + 1) : i;
				break;
			case 0b00:
				var_assign(config, i, 1);
				break;
		}
	}
}

int sat_count(bitstore * cconf)
{
	int c = 0;
	for (int i = 0; i < cconf_len; i++)
		c += count_bits(cconf[i]);
	return c;
}

int all_satisfied(bitstore * cconf)
{
	return sat_count(cconf) == n_clauses;
}

bitstore * copy_config(bitstore * config)
{
	bitstore * cfg = malloc(cfg_size);
	return memcpy(cfg, config, cfg_size);
}

int lit_choose_starting(bitstore * config, int n)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	for (int i = n; i <= n_vars; i++)
		if (ass_state(nconf, pconf, i) == 0b00)
			return i;
	for (int i = 1; i < n; i++)
		if (ass_state(nconf, pconf, i) == 0b00)
			return i;
	return 0;
}

int lit_choose_first(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	for (int i = 1; i <= n_vars; i++)
		if (ass_state(nconf, pconf, i) == 0b00)
			return i;
	return 0;
}

int lit_choose_last(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	for (int i = n_vars; i > 0; i++)
		if (ass_state(nconf, pconf, i) == 0b00)
			return i;
	return 0;
}

int lit_occurrence_count(bitstore * cconf, int lit)
{
	int c = 0;
	bitstore * occurlist = occurlists[lit];

	for (int i = 0; i < cconf_len; i++)
		c += count_bits(~cconf[i] & occurlist[i]);

	return c;
}

int var_occurrence_count(bitstore * cconf, int var)
{
	return
		lit_occurrence_count(cconf, var) +
		lit_occurrence_count(cconf, -var);
}

int lit_choose_max_occur_var(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int max = 0;
	int max_i;

	for (int i = 1; i <= n_vars; i++) {
		if (ass_state(nconf, pconf, i) == 0b00) {
			int n_occ = var_occurrence_count(config, i);
			if (n_occ > max) {
				max = n_occ;
				max_i = i;
			}
		}
	}

	return max_i;
}

typedef
struct pair_tag {
	int a, b;
} pair;

pair lo_count_power(bitstore * config, int lit)
{
	bitstore * cconf = config;

	bitstore * occurlist = occurlists[lit];
	int c = 0;
	int p = 0;

	for (int i = 0; i < cconf_len; i++) {
		bitstore occ = ~cconf[i] & occurlist[i];
		while (occ) {
			int pos = least_bit_pos(occ);
			c++;
			if (clause_length(config, i * 8 * sizeof occ + pos) == 2) p++;
			occ &= ~bit(pos);
		}
		
		// while (occ) {
			// if (occ & 1U) {
				// c++;
				// if (clause_length(config, clause_i) == 2) p++;
			// }
			// occ >>= 1;
			// clause_i++;
		// }
	}

	return (pair){ c, p };
}

int lit_choose_max_occur_power(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int max = -1;
	int max_i = 0;

	for (int var = 1; var <= n_vars; var++)
	if (ass_state(nconf, pconf, var) == 0b00) {
		pair cp_pos = lo_count_power(config, var);
		pair cp_neg = lo_count_power(config, -var);
		
		int unsat_count = n_clauses - sat_count(config);
		int f = round(mean_occ_len * unsat_count / n_clauses);
		int score_pos = cp_pos.a + f * cp_neg.b;
		int score_neg = cp_neg.a + f * cp_pos.b;

		int temp = score_pos;
		score_pos += score_neg * 0.75;
		score_neg += temp * 0.75;

		if (score_pos > max) max = score_pos, max_i = var;
		if (score_neg > max) max = score_neg, max_i = -var;
	}

	return max_i;
}

int lit_choose_min_occur_var(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int min = 2 * n_clauses;
	int min_i;

	for (int i = 1; i <= n_vars; i++) {
		if (ass_state(nconf, pconf, i) == 0b00) {
			int n_occ = var_occurrence_count(config, i);
			if (n_occ < min) {
				min = n_occ;
				min_i = i;
			}
		}
	}

	return min_i;
}

int lit_choose_max_occur_lit(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int max = 0;
	int max_i;

	for (int i = 1; i <= n_vars; i++) {
		if (ass_state(nconf, pconf, i) == 0b00) {
			int n_occ_pos = var_occurrence_count(config, i);
			int n_occ_neg = var_occurrence_count(config, -i);
			if (n_occ_pos > max) {
				max = n_occ_pos;
				max_i = i;
			}
			if (n_occ_neg > max) {
				max = n_occ_neg;
				max_i = -i;
			}
		}
	}

	return max_i;
}

int lit_choose_min_occur_lit(bitstore * config)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	int min = n_clauses;
	int min_i;

	for (int i = 1; i <= n_vars; i++) {
		if (ass_state(nconf, pconf, i) == 0b00) {
			int n_occ_pos = var_occurrence_count(config, i);
			int n_occ_neg = var_occurrence_count(config, -i);
			if (n_occ_pos < min) {
				min = n_occ_pos;
				min_i = i;
			}
			if (n_occ_neg < min) {
				min = n_occ_neg;
				min_i = -i;
			}
		}
	}

	return min_i;
}

void sanity(bitstore * config)
{
	bitstore * cconf = config;
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	for (int i = 1; i <= n_clauses; i++) {
		bitstore * pclause = clauses[i];
		bitstore * nclause = clauses[-i];
		int ok = 0;
		if (is_s_set(cconf, i)) {
			for (int j = 0; j < olconf_len; j++) {
				if (pclause[j] & pconf[j] || nclause[j] & nconf[j]) {
					ok = 1;
					break;
				}
			}
			if (!ok)
				printf("insanity: c%d satisfied, no lits of it is true\n", i);
		}
		else {
			ok = 1;
			for (int j = 0; j < olconf_len; j++) {
				if (pclause[j] & pconf[j] || nclause[j] & nconf[j]) {
					ok = 0;
					printf("insanity: c%d unsat, with some lits true\n", i);
					break;
				}
			}
		}

		if (!ok) {
			puts("something's not ok");
		}
	}
}

bitstore * dpll_rec(bitstore * config)
{
	if (!c_len_reductions(config)) {
		free(config);
		return NULL;
	}
	purity_reduction(config);
	if (all_satisfied(config)) return config;

	bitstore * configA = copy_config(config);
	bitstore * configB = config;

	int choice = lit_choose_max_occur_power(config);
	if (choice == 0) {
		puts("This shouldn't happen.");
		sanity(config);
		free(config);
		return NULL;
	}

	lit_assign(configA, choice);
	configA = dpll_rec(configA);
	if (configA) {
		free(configB);
		return configA;
	}

	lit_assign(configB, -choice);
	return dpll_rec(configB);
}

bitstore * dpll_depth(void)
{
	bitstore * config = calloc(cfg_len, sizeof * config);
	return dpll_rec(config);
}

typedef
enum dpll_result_tag {
	TBD,
	FAIL,
	SUCCESS
} dpll_result;

dpll_result dpll_step(bitstore * config)
{
	if (!c_len_reductions(config))
		return FAIL;
	purity_reduction(config);
	if (all_satisfied(config))
		return SUCCESS;

	return TBD;
}

bitstore * dpll_breadth(void)
{
	size_t length = (1ULL << 18) / cfg_size;
	bitstore * prealloc = malloc(length * cfg_size);
	dpll_result * results = malloc(length * sizeof * results);

	if (prealloc == NULL || results == NULL) {
		fprintf(stderr, "Need more memory than system allows.\n");
		return NULL;
	}

	memset(prealloc, 0, length * cfg_size);
	results[0] = TBD;

	int nTBD = 1;
	int last = 1;

	// continue until all become FAILs and one becomes SUCCESS
	// last will remain the same, if all none turned out TBD or SUCCESS
	while (nTBD) {
		if (nTBD < last / 2 || last > length / 2) {
			// int old_last = last;
			last--;
			for (int i = 0; i <= last; i++) if (results[i] == FAIL) {
				memcpy(prealloc + i * cfg_len, prealloc + last-- * cfg_len, cfg_size);
				results[i] = TBD; // we know it's not FAIL nor SUCCESS
				while (results[last] == FAIL) last--;
			}
			last++;
			// printf("Consolidation compressed it by %.2f%%\n", 100.0 * last / old_last);
		}
		if (last > length / 2) {
			length *= 2;
			prealloc = realloc(prealloc, length * cfg_size);
			results = realloc(results, length * sizeof * results);
			// printf("size increase!\n");
			if (prealloc == NULL || results == NULL) {
				fprintf(stderr, "Need more memory than system allows.\n");
				return NULL;
			}
		}

		nTBD = 0;

		for (int i = last - 1; i >= 0; i--) if (results[i] == TBD) {
			bitstore * exhibit = prealloc + i * cfg_len;
			bitstore * exhibitA;
			bitstore * exhibitB;
			int choice;

			switch (results[i] = dpll_step(exhibit)) {
				case TBD:
					choice = lit_choose_max_occur_power(exhibit);
					if (choice != 0) {
						exhibitA = exhibit;
						exhibitB = memcpy(prealloc + last * cfg_len, exhibit, cfg_size);

						lit_assign(exhibitA, choice);
						lit_assign(exhibitB, -choice);

						results[last++] = TBD;
						nTBD += 2;

						break;
					}

					results[i] = FAIL;
					puts("This shouldn't happen.");
				case FAIL:
					break;
				case SUCCESS:
					exhibit = copy_config(exhibit);
					free(prealloc);
					free(results);
					return exhibit;
			}
		}
	}

	free(prealloc);
	free(results);
	return NULL;
}

void print_assignments(bitstore * config, FILE * stream)
{
	bitstore * nconf = config + cconf_len;
	bitstore * pconf = nconf + olconf_len;

	for (int i = 1; i <= n_vars; i++) {
		switch (ass_state(nconf, pconf, i)) {
			case 0b00:
				printf("Var #%d is unset\n", i);
			case 0b01:
				fprintf(stream, "%d 1\n", i);
				break;
			case 0b10:
				fprintf(stream, "%d 0\n", i);
				break;
			case 0b11:
				printf("Var #%d is set for both\n", i);
		}
	}
}

int main(int argc, char const *argv[])
{
	if (argc < 2) {
		fprintf(stderr, "Usage: %s problem.cnf\n", argv[0]);
		return -1;
	}

	FILE * fp = fopen(argv[1], "r");
	if (fp == NULL) {
		perror("Error opening file.");
		return -1;
	}

	FILE * fw = NULL;
	if (argc == 3) {
			fw = fopen(argv[2], "w");
			if (fw == NULL) {
					perror("Error opening file to write.");
					return -1;
			}
	}

	if (!read(fp)) {
		fputs("Formula couldn't be read\n", stderr);
		return -1;
	}

	bitstore * config = dpll_breadth();

	if (config == NULL) {
		puts("Unsatisfiable.");
	}
	else {
		puts("Satisfiable!");
		print_assignments(config, (fw == NULL) ? stdout : fw);
		free(config);
	}

	clean_formula();

	return 0;
}
