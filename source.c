#include <stdio.h>
#include <stdlib.h>
#define BUFSIZ 1024
#define EXPLPC 4

typedef
struct Formula_tag
{
	int * lits;
	int * off_clauses;
	int n_lits;
	int n_clauses;
} Formula;


Formula read(FILE * fp)
{
	Formula result = { NULL, NULL, 0, 0 };

	char buffer[BUFSIZ];
	char * bufptr;

	int n_vars;

	while (fgets(buffer, BUFSIZ, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else if (*buffer == 'p') {
			// the spec
			if (sscanf(buffer, "p cnf %d %d", &n_vars, &result.n_clauses) != 2) {
				fputs(stderr, "Error at the spec line.");
				return result;
			}
			break;
		}
		else {
			fputs(stderr, "Couldn't find spec line as the first non-comment line.\n");
			return result;
		}
	}

	result.n_lits = result.n_clauses * EXPLPC;

	// memory for all the literals and clause offsets
	result.lits = malloc(result.n_lits * sizeof * result.lits);
	result.off_clauses = calloc(result.n_clauses, sizeof * result.off_clauses);

	int * p_lit = result.lits;
	int * lim_lit = p_lit + result.n_lits;

	int i_clause = 0;

	while (i_clause < result.n_clauses && fgets(buffer, BUFSIZ, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else {
			// a clause
			int i_lit = 0;
			char * token = strtok(buffer, " ");

			while (token != NULL)
			{
				if (p_lit >= lim_lit) {
					result.lits = realloc(result.lits, 2 * result.n_lits * sizeof * result.lits);
					p_lit = result.lits + result.n_lits;
					lim_lit = result.lits + 2 * result.n_lits;
					result.n_lits *= 2;
				}

				*p_lit = atoi(token);
				if (*p_lit == 0) {
					break;
				}

				token = strtok(NULL, " ");
				p_lit++;
				i_lit++;
			}

			result.off_clauses[i_clause] =

			i_clause++;
		}
	}

	if (i_clause != result.n_clauses) {
		fprintf(stderr, "%d/%d clauses are missing.\n", result.n_clauses - i_clause, result.n_clauses);
		free(result.lits);
		return result;
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		free(result.lits);
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
