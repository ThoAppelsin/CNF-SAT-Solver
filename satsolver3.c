#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BUFFERSIZE 1024
#define EXPLPC 4

typedef uint32_t bitstore;

#define sbitstore (8 * sizeof(bitstore))
#define bit(x) (1U << (x))
#define mask(x, y) ((x) & bit(y))
#define sset(s, i) mask((s)[(i) / sbitstore], (i) % sbitstore)

int n_clauses;
int n_vars;
int ** clauses;
int ** occurlists;

int c_conf_size;
int ol_conf_size;
int cfg_size;

void init_globals(void) {
	assert(sbitstore == 32);

	c_conf_size = (n_clauses - 1) / sbitstore + 1;
	ol_conf_size = n_vars / sbitstore + 1;
	cfg_size = (c_conf_size + 2 * ol_conf_size) * sizeof(bitstore);
}

void init_formula(void)
{
	clauses = malloc(n_clauses * sizeof * clauses);
	occurlists = malloc((2 * n_vars + 1) * sizeof * occurlists);
	occurlists += n_vars;

	for (int i = 0; i < n_clauses; i++) {
		clauses[i] = calloc(EXPLPC + 2, sizeof * clauses[i]);
		clauses[i][EXPLPC + 1] = -1;
	}
	for (int i = 1; i <= n_vars; i++) {
		occurlists[i] = malloc((n_clauses + 1) * sizeof * occurlists[i]);
		occurlists[-i] = malloc((n_clauses + 1) * sizeof * occurlists[-i]);
		occurlists[i][0] = 0;
		occurlists[-i][0] = 0;
	}
}

void clean_formula(void)
{
	for (int i = 0; i < n_clauses; i++) free(clauses[i]);
	for (int i = 1; i <= n_vars; i++) {
		free(occurlists[i]);
		free(occurlists[-i]);
	}
	free(clauses);
	free(occurlists - n_vars);
}

int p_i_clause = 0;

void lits_add(int lit, int i_clause)
{
	assert(i_clause >= p_i_clause);
	p_i_clause = i_clause;

	int * clause = clauses[i_clause];
	if (clause[++clause[0]] == -1) {
		clause = clauses[i_clause] = realloc(clause, (clause[0] * 2 + 1) * sizeof * clause);
		memset(clause + clause[0] + 1, 0, (clause[0] - 1) * sizeof * clause);
		clause[clause[0] * 2] = -1;
	}
	clause[clause[0]] = lit;

	int * occurlist = occurlists[lit];
	if (occurlist[0] && occurlist[occurlist[0]] == i_clause) return;
	occurlist[++occurlist[0]] = i_clause;
}

int read(FILE * fp)
{
	char buffer[BUFFERSIZE];

	while (fgets(buffer, BUFFERSIZE, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else if (*buffer == 'p') {
			// the spec
			if (sscanf(buffer, "p cnf %d %d", &n_vars, &n_clauses) != 2) {
				fputs("Error at the spec line.\n", stderr);
				return 0;
			}
			break;
		}
		else {
			fputs("Couldn't find spec line as the first non-comment line.\n", stderr);
			return 0;
		}
	}

	init_formula();

	int i_clause = 0;
	while (i_clause < n_clauses && fgets(buffer, BUFFERSIZE, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else {
			// a clause
			int lit;
			char * token = strtok(buffer, " ");

			while (token != NULL)
			{
				lit = atoi(token);
				if (lit == 0) break;

				lits_add(lit, i_clause);
				token = strtok(NULL, " ");
			}

			i_clause++;
		}
	}

	if (i_clause != n_clauses) {
		fprintf(stderr, "%d/%d clauses are missing.\n", n_clauses - i_clause, n_clauses);
		return 0;
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		return 0;
	}

	return 1;
}

int lit_occurs_clause(int lit, int i_clause)
{
	int * clause = clauses[i_clause];
	for (int i = 1; i <= clause[0]; i++)
		if (clause[i] == lit)
			return 1;
	return 0;
}

void lit_propagate(bitstore * cconf, int lit)
{
	int * occurlist = occurlists[lit];
	for (int i = 1; i <= occurlist[0]; i++) {
		assert(occurlist[i] / sbitstore < c_conf_size);
		assert(lit_occurs_clause(lit, occurlist[i]));

		// mark the occurlist[i]th clause as satisfied
		cconf[occurlist[i] / sbitstore] |= bit(occurlist[i] % sbitstore);
	}
}

void var_assign(bitstore * config, int var, int ispos)
{
	bitstore * cconf = config;
	bitstore * nconf = config + c_conf_size;
	bitstore * pconf = nconf + ol_conf_size;

	bitstore * xconf;
	int lit;

	if (ispos) xconf = pconf, lit = var;
	else       xconf = nconf, lit = -var;
	
	xconf[var / sbitstore] |= bit(var % sbitstore);
	lit_propagate(cconf, lit);
}

int c_len_reductions(bitstore * config)
{
	bitstore * cconf = config;
	bitstore * nconf = config + c_conf_size;
	bitstore * pconf = nconf + ol_conf_size;

	int last_edit = n_clauses;

	for (int i = 0; i != last_edit; i++) {
		if (i == n_clauses) i = 0;

		assert(i / sbitstore < c_conf_size);
		// sset of cconf at i, signifies that the clause i is satisfied
		if (sset(cconf, i)) continue;

		int * clause = clauses[i];
		int clen = 0;
		int u_var, u_ispos;
		for (int j = 1; j <= clause[0]; j++) {
			int lit = clause[j];
			int var = abs(lit);
			int ispos = lit > 0;

			assert(lit != 0);
			
			// if the literal is set to its opposite, it is not there
			// sset of nconf at var, signifies that var is set to False
			// sset of pconf at var, signifies that var is set to True
			if (!sset(ispos ? nconf : pconf, var)) {
				clen++;
				u_var = var;
				u_ispos = ispos;
			}
		}
		switch (clen) {
			case 0: return 0;
			case 1:
				assert(u_var / sbitstore < ol_conf_size);

				var_assign(config, u_var, u_ispos);
				last_edit = i ? i : n_clauses;
		}
	}

	return 1;
}

unsigned int e_occurrence_unsat(bitstore * cconf, int lit)
{
	int * occurlist = occurlists[lit];
	for (int i = 1; i <= occurlist[0]; i++)
		// return True if even one clause that it occurs is still not satisfied
		if (!sset(cconf, occurlist[i]))
			return 1U;
	return 0U;
}

unsigned int var_state(bitstore * cconf, int var)
{
	return e_occurrence_unsat(cconf, -var) << 1 | e_occurrence_unsat(cconf, var);
}

unsigned int ass_state(bitstore * nconf, bitstore * pconf, int var)
{
	return !!sset(nconf, var) << 1 | !!sset(pconf, var);
}

void purity_reduction(bitstore * config)
{
	bitstore * cconf = config;
	bitstore * nconf = config + c_conf_size;
	bitstore * pconf = nconf + ol_conf_size;

	int last_edit = n_vars + 1;

	for (int i = 1; i != last_edit; i++) {
		if (i == n_vars + 1) i = 1;

		// skip the variables already set True/False
		if (sset(pconf, i) || sset(nconf, i)) continue;

		switch (var_state(cconf, i)) {
			case 0b01:
				assert(i / sbitstore < ol_conf_size);
				assert(e_occurrence_unsat(cconf, i) && !e_occurrence_unsat(cconf, -i));
				var_assign(config, i, 1);
				last_edit = (i == 1) ? (n_vars + 1) : i;
				break;
			case 0b10:
				assert(i / sbitstore < ol_conf_size);
				assert(!e_occurrence_unsat(cconf, i) && e_occurrence_unsat(cconf, -i));
				var_assign(config, i, 0);
				last_edit = (i == 1) ? (n_vars + 1) : i;
				break;
			case 0b00:
				var_assign(config, i, 1);
				break;
		}
	}
}

int all_satisfied(bitstore * cconf)
{
	for (int i = 0; i < n_clauses; i++)
		// return False if any clause left unsatisfied
		if (!sset(cconf, i))
			return 0;
	return 1;
}

bitstore * copy_config(bitstore * config)
{
	bitstore * cfg = malloc(cfg_size);
	return memcpy(cfg, config, cfg_size);
}

int lit_choose(bitstore * config)
{
	bitstore * nconf = config + c_conf_size;
	bitstore * pconf = nconf + ol_conf_size;

	for (int i = 1; i <= n_vars; i++)
		if (ass_state(nconf, pconf, i) == 0b00)
			return i;
	return 0;
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

	int choice = lit_choose(config);
	if (choice == 0) {
		puts("This shouldn't happen.");
		free(config);
		return NULL;
	}

	var_assign(configA, choice, 1);
	configA = dpll_rec(configA);
	if (configA) {
		free(configB);
		return configA;
	}

	var_assign(configB, choice, 0);
	return dpll_rec(configB);
}

bitstore * dpll(void)
{
	bitstore * config = calloc(c_conf_size + 2 * ol_conf_size, sizeof * config);
	return dpll_rec(config);
}

void print_assignments(bitstore * config, FILE * stream)
{
	bitstore * nconf = config + c_conf_size;
	bitstore * pconf = nconf + ol_conf_size;

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

	init_globals();
	bitstore * config = dpll();

	if (config == NULL) {
		puts("Unsatisfiable.");
	}
	else {
		puts("Satisfiable!");
		print_assignments(config, stdout);
		if (fw != NULL) {
			print_assignments(config, fw);
		}
		free(config);
	}

	clean_formula();

	return 0;
}
