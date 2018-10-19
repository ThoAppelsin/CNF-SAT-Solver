#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define BUFFERSIZE 1024
#define EXPLPC 4

typedef
struct Formula_tag
{
	int n_vars;			// variable count, constant during dpll
	int n_clauses;		// clause count, decreases during dpll
	int n_lits;			// literal count, constant during dpll
	int ** occurlist;		// list (n_vars + 1) of null-terminated, non-zero arrays (arbitrary)
	int * off_clauses;		// array (n_clauses + 1) of increasing numbers, starting with zero
	int * lits;				// list (n_lits) of literals for the whole formula
								// zero implies absence of literal, n_vars + 1 is a clause boundary
	int i_lit;
} Formula;

Formula * new_formula(int n_vars, int n_clauses)
{
	Formula * result = malloc(sizeof * result);

	result->n_vars = n_vars;
	result->n_clauses = n_clauses;
	result->n_lits = n_clauses * EXPLPC;

	// plus 1 is for variable names starting with 1
	result->occurlist = calloc(result->n_vars + 1, sizeof * result->occurlist);
	// plus 1 is for algorithm's efficiency
	result->off_clauses = malloc((result->n_clauses + 1) * sizeof * result->off_clauses);
	result->lits = malloc(result->n_lits * sizeof * result->lits);

	result->i_lit = 0;

	return result;
}

void del_formula(Formula * formula)
{
	for (int i = 0; i < formula->n_vars; i++)
		if (formula->occurlist[i])
			free(formula->occurlist[i]);

	free(formula->occurlist);
	free(formula->off_clauses);
	free(formula->lits);

	free(formula);
}

void occurlist_add(Formula * formula, int var, int offset)
{
	if (formula->occurlist[var] == NULL) {
		formula->occurlist[var] = malloc(EXPLPC * sizeof * formula->occurlist[var]);
		formula->occurlist[var][0] = offset;
		formula->occurlist[var][1] = 0;
		formula->occurlist[var][EXPLPC - 1] = -1;
		return;
	}

	int end = 0;
	while (formula->occurlist[var][end] > 0) end++;

	formula->occurlist[var][end++] = offset;
	if (formula->occurlist[var][end] == -1) {
		formula->occurlist[var] = realloc(formula->occurlist[var], 2 * (end + 1) * sizeof * formula->occurlist[var]);
		formula->occurlist[var][2 * end + 1] = -1;
	}
	formula->occurlist[var][end] = 0;
}

void occurlist_remove(Formula * formula, int var, int offset)
{
	for (int * occur = formula->occurlist[var]; *occur != 0; occur++) {
		if (*occur == offset) {
			while (*occur != 0) {
				*occur = *(occur + 1);
				occur++;
			}
			break;
		}
	}
}

int * clause_get(Formula * formula, int i)
{
	return formula->lits + formula->off_clauses[i];
}

int clause_maxlen(Formula * formula, int i)
{
	return formula->off_clauses[i + 1] - formula->off_clauses[i];
}

int clause_length(Formula * formula, int clause_i)
{
	int * clause = clause_get(formula, clause_i);
	int len = 0;
	int maxlen = clause_maxlen(formula, clause_i);
	for (int i = 0; i < maxlen && clause[i] != formula->n_vars + 1; i++)
		if (clause[i] != 0)
			len++;
	return len;
}

void clause_remove(Formula * formula, int clause_i)
{
	int * clause = clause_get(formula, clause_i);

	int maxlen = clause_maxlen(formula, clause_i);
	for (int i = 0; i < maxlen && clause[i] != formula->n_vars + 1; i++)
		if (clause[i] != 0)
			occurlist_remove(formula, clause[i], formula->off_clauses[clause_i] + i);

	clause[0] = formula->n_vars + 1;

	for (int i = clause_i; i < formula->n_clauses - 1; i++) {
		formula->off_clauses[i] = formula->off_clauses[i + 1];
	}

	formula->n_clauses--;
}

int binary_search(int * arr, int len, int x)
{
	int start = 0;
	int end = len;

	while (start < end) {
		int mid = (start + end) / 2;
		if (x < arr[mid])
			end = mid;
		else
			start = mid + 1;
	}

	return start - 1;
}

int clause_i_for_offset(Formula * formula, int offset)
{
	return binary_search(formula->off_clauses, formula->n_clauses + 1, offset);
}

void lits_add(Formula * formula, int lit)
{
	if (formula->i_lit >= formula->n_lits) {
		formula->n_lits *= 2;
		formula->lits = realloc(formula->lits, formula->n_lits * sizeof * formula->lits);
	}

	occurlist_add(formula, abs(lit), formula->i_lit);
	formula->lits[formula->i_lit++] = lit;
}

void lits_remove(Formula * formula, int offset)
{
	occurlist_remove(formula, formula->lits[offset], offset);
	formula->lits[offset] = 0;
}

Formula * read(FILE * fp)
{
	char buffer[BUFFERSIZE];

	int n_vars = 0;
	int n_clauses = 0;

	while (fgets(buffer, BUFFERSIZE, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else if (*buffer == 'p') {
			// the spec
			if (sscanf(buffer, "p cnf %d %d", &n_vars, &n_clauses) != 2) {
				fputs("Error at the spec line.\n", stderr);
				return NULL;
			}
			break;
		}
		else {
			fputs("Couldn't find spec line as the first non-comment line.\n", stderr);
			return NULL;
		}
	}

	Formula * result = new_formula(n_vars, n_clauses);

	int i_clause = 0;
	result->off_clauses[i_clause] = 0;

	while (i_clause < result->n_clauses && fgets(buffer, BUFFERSIZE, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else {
			// a clause
			int i_lit = 0;
			int lit;
			char * token = strtok(buffer, " ");

			while (token != NULL)
			{
				lit = atoi(token);
				if (lit == 0) break;

				lits_add(result, lit);
				token = strtok(NULL, " ");
				i_lit++;
			}

			result->off_clauses[i_clause + 1] = result->off_clauses[i_clause] + i_lit;

			i_clause++;
		}
	}

	if (i_clause != result->n_clauses) {
		fprintf(stderr, "%d/%d clauses are missing.\n", result->n_clauses - i_clause, result->n_clauses);
		free(result->lits);
		return result;
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		free(result->lits);
		return result;
	}

	return result;
}

int unit_propagate(Formula * formula, int clause_i)
{
	int var = clause_get(formula, clause_i)[0];
	int * occur = formula->occurlist[var];

	while (*occur != 0) {
		if (formula->lits[*occur] == var) {
			clause_remove(formula, clause_i_for_offset(formula, *occur));
		}
		else {
			lits_remove(formula, *occur);
		}
	}
}

int dpll(Formula * formula)
{
	int * uc_indices = malloc(formula->n_clauses * sizeof * uc_indices);
	int uc_indices_size = 0;

	for (int i = 0; i < formula->n_clauses; i++) {
		int len_clause = clause_length(formula, i);

		switch (len_clause)
		{
			case 0: return 0;
			case 1:
				uc_indices[uc_indices_size++] = i;
				break;
		}
	}

	int * clauses_to_delete = calloc(formula->n_clauses, sizeof * clauses_to_delete);
	for (int i = 0; i < uc_indices_size; i++) {
	}
}

int main(int argc, char const *argv[])
{
	if (argc != 2) {
		fputs("Usage: ugsat problem.cnf\n", stderr);
		return -1;
	}

	FILE * fp = fopen(argv[1], "r");
	if (fp == NULL) {
		perror("Error opening file.");
		return -1;
	}

	Formula * formula = read(fp);
	if (formula == NULL) {
		return -1;
	}

	dpll(formula);

	return 0;
}
