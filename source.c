#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define BUFFERSIZE 1024
#define EXPLPC 4
#define OL_END -1
#define OL_FIN -2

typedef
struct Formula_tag
{
	int n_vars;			// variable count, constant during dpll
	int n_clauses;		// clause count, decreases during dpll
	int n_lits;			// literal count, constant during dpll
	int ** occurlist;		// list (n_vars + 1) of min1-terminated, non-zero arrays (arbitrary)
	int * off_clauses;		// array (n_clauses + 1) of increasing numbers, starting with zero
	int * lits;				// list (n_lits) of literals for the whole formula
								// zero implies absence of literal, n_vars + 1 is a clause boundary
	int i_lit;
} Formula;

typedef
struct Pair_tag
{
	int a;
	int b;
} Pair;

void occurlist_add(Formula * formula, int var, int offset)
{
	if (formula->occurlist[var] == NULL) {
		formula->occurlist[var] = malloc(EXPLPC * sizeof * formula->occurlist[var]);
		formula->occurlist[var][0] = offset;
		formula->occurlist[var][1] = OL_END;
		formula->occurlist[var][EXPLPC - 1] = OL_FIN;
		return;
	}

	int end = 0;
	while (formula->occurlist[var][end] > OL_END) end++;

	formula->occurlist[var][end++] = offset;
	if (formula->occurlist[var][end] == OL_FIN) {
		formula->occurlist[var] = realloc(formula->occurlist[var], 2 * (end + 1) * sizeof * formula->occurlist[var]);
		formula->occurlist[var][2 * end + 1] = OL_FIN;
	}
	formula->occurlist[var][end] = OL_END;
}

void occurlist_lit_remove(Formula * formula, int offset)
{
	int var = abs(formula->lits[offset]);
	for (int * occur = formula->occurlist[var]; *occur != OL_END; occur++) {
		if (*occur == offset) {
			while (*occur != OL_END) {
				*occur = *(occur + 1);
				occur++;
			}
			break;
		}
	}
}

void occurlist_var_remove(Formula * formula, int var)
{
	if (formula->occurlist[var] != NULL) {
		free(formula->occurlist[var]);
		formula->occurlist[var] = NULL;
	}
}

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

Formula * del_formula(Formula * formula)
{
	for (int i = 1; i < formula->n_vars; i++)
		occurlist_var_remove(formula, i);

	free(formula->occurlist);
	free(formula->off_clauses);
	free(formula->lits);

	free(formula);
	return NULL;
}

int * clause_get(Formula * formula, int i)
{
	return formula->lits + formula->off_clauses[i];
}

int clause_maxlen(Formula * formula, int i)
{
	return formula->off_clauses[i + 1] - formula->off_clauses[i];
}

Pair clause_length(Formula * formula, int clause_i)
{
	int * clause = clause_get(formula, clause_i);
	Pair len_last = { 0, 0 };
	int maxlen = clause_maxlen(formula, clause_i);
	for (int i = 0; i < maxlen && clause[i] != formula->n_vars + 1; i++) {
		if (clause[i] != 0) {
			len_last.a++;
			len_last.b = clause[i];
		}
	}
	return len_last;
}

void clause_remove(Formula * formula, int clause_i)
{
	int * clause = clause_get(formula, clause_i);

	int maxlen = clause_maxlen(formula, clause_i);
	for (int i = 0; i < maxlen && clause[i] != formula->n_vars + 1; i++)
		if (clause[i] != 0)
			occurlist_lit_remove(formula, formula->off_clauses[clause_i] + i);

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
	occurlist_lit_remove(formula, offset);
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
		return del_formula(result);
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		return del_formula(result);
	}

	return result;
}

// returns the new would-be index (it should be removed now) of the clause
int unit_propagate(Formula * formula, int clause_i, int unit)
{
	int var = abs(unit);
	int * occur = formula->occurlist[var];
	int shift = 0;

	while (*occur != OL_END) {
		if (formula->lits[*occur] == unit) {
			int ci = clause_i_for_offset(formula, *occur);
			if (formula->off_clauses[ci] <= formula->off_clauses[clause_i])
				shift++;
			clause_remove(formula, ci);
		}
		else {
			lits_remove(formula, *occur);
		}
	}

	occurlist_var_remove(formula, var);

	return clause_i - shift;
}

// since unit propagation may introduce new unit clauses, this repeats itself until no change
int empty_clause_and_unit_propagate(Formula * formula)
{
	int retry_until = 0;
	int i = 0;

	do for (i = 0; i < formula->n_clauses && i != retry_until; i++) {
		Pair len_last = clause_length(formula, i);

		switch (len_last.a)
		{
			case 0: return 0;
			case 1:
				i = unit_propagate(formula, i, len_last.b);
				retry_until = i;
				break;
		}
	} while (i != retry_until);
}

int get_occurence(Formula * formula, int var, int i)
{
	if (formula->occurlist[var][i] == OL_END) return 0;
	return formula->lits[formula->occurlist[var][i]];
}

int get_pure(Formula * formula, int var)
{
	if (formula->occurlist[var] == NULL) return 0;

	int candidate = get_occurence(formula, var, 0);
	if (candidate == 0) return 0;

	for (int i = 1; ; i++) {
		int offender = get_occurence(formula, var, i);
		if (offender == 0) return candidate;
		if (offender != candidate) return 0;
	}
}

void pure_literal_propagate(Formula * formula, int var)
{
	int * occur = formula->occurlist[var];
	while (*occur != OL_END)
		clause_remove(formula, clause_i_for_offset(formula, *occur));

	free(formula->occurlist[var]);
	formula->occurlist[var] = NULL;
}

// since pure literal propagations may introduce new ones, this repeats itself until no change
void pure_literal_assignment(Formula * formula)
{
	int retry_until = 1;
	int var = 1;

	do for (var = 1; var < formula->n_vars && var != retry_until; var++) {
		int pure = get_pure(formula, var);
		if (pure == 0) continue;

		pure_literal_propagate(formula, var);
	} while (var != retry_until);
}

int dpll(Formula * formula)
{
	int empty_clause = !empty_clause_and_unit_propagate(formula);
	if (empty_clause) return 0;
	pure_literal_assignment(formula);
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
