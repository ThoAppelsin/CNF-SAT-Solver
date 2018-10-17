#include <stdio.h>
#include <stdlib.h>
#define BUFSIZ 1024
#define EXPLPC 4

typedef
struct Formula_tag
{
	int n_vars;
	int n_clauses;
	int n_lits;
	int ** occurlist;
	int * off_clauses;
	int * lits;
	int i_lit;
} Formula;

Formula * new_formula(int n_vars, int n_clauses)
{
	Formula * result = malloc(sizeof * result);

	result->n_vars = n_vars;
	result->n_clauses = n_clauses;
	result->n_lits = n_clauses * EXPLPC;

	result->occurlist = calloc(result->n_vars, sizeof * result->occurlist);
	// plus 1 is for algorithm's efficiency
	result->off_clauses = calloc(result->n_clauses + 1, sizeof * result->off_clauses);
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
	if (!formula->occurlist[var]) {
		formula->occurlist[var] = malloc(EXPLPC * sizeof * formula->occurlist[var]);
		formula->occurlist[var][0] = offset;
		formula->occurlist[var][1] = 0;
		formula->occurlist[var][EXPLPC - 1] = -1;
		return;
	}

	int end = 0;
	while (formula->occurlist[var][end++]);

	formula->occurlist[var][end - 1] = offset;
	if (formula->occurlist[var][end] == -1) {
		formula->occurlist[var] = realloc(formula->occurlist[var], 2 * (end + 1) * sizeof * formula->occurlist[var]);
		formula->occurlist[var][2 * end + 1] = -1;
	}
	formula->occurlist[var][end] = 0;
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

Formula * read(FILE * fp)
{
	char buffer[BUFSIZ];
	char * bufptr;

	int n_vars;
	int n_clauses;

	while (fgets(buffer, BUFSIZ, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else if (*buffer == 'p') {
			// the spec
			if (sscanf(buffer, "p cnf %d %d", &n_vars, &n_clauses) != 2) {
				fputs(stderr, "Error at the spec line.");
				return NULL;
			}
			break;
		}
		else {
			fputs(stderr, "Couldn't find spec line as the first non-comment line.\n");
			return NULL;
		}
	}

	Formula * result = new_formula(n_vars, n_clauses);

	int i_clause = 0;

	while (i_clause < result->n_clauses && fgets(buffer, BUFSIZ, fp) != NULL)
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

int main(int argc, char const *argv[])
{
	if (argc != 2) {
		fputs(stderr, "Usage: ugsat problem.cnf\n");
		return -1;
	}

	FILE * fp = fopen(argv[1], "r");
	if (fp = NULL) {
		perror("Error opening file.");
		return -1;
	}

	read(fp);

	return 0;
}
