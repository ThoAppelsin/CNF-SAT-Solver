#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BUFFERSIZE 1024
#define EXPLPC 4

#define sign(x) ((x) >= 0 ? 1 : -1)
#define bit(n) (1U << (n))

#define OL_START_POS -1
#define OL_LEN -2
#define CL_NONE -1

typedef
struct Formula_tag
{
	int n_vars;			// variable count, constant during dpll
	int n_clauses;		// clause count, decreases during dpll
	int n_clauses_init; // clause count as of beginning, constant
	int n_lits;			// literal count, constant during dpll
	int ** occurlists;		// 0-centered list (2 * n_vars + 1) of arrays of clause indices
								// 1-indexed unique & increasing arrays
								// 0th index is for length
	int * off_clauses;		// array (n_clauses + 1) of increasing numbers, starting with zero
	int * lits;				// list (n_lits) of literals for the whole formula
								// zero implies absence of literal, n_vars + 1 is a clause boundary
	int i_lit;
	int * assignments;		// 1-indexed list of (n_vars) of +/- 1s
} Formula;

void secure_free(void * ptr)
{
	if (ptr != NULL) free(ptr);
}

int ceiling_binary_search(int * arr, int len, int x)
{
	int start = 0;
	int end = len;

	while (start < end) {
		int mid = (start + end) / 2;
		if (arr[mid] < x)
			start = mid + 1;
		else
			end = mid;
	}

	return start;
}

int flooring_binary_search(int * arr, int len, int x)
{
	return ceiling_binary_search(arr, len, x + 1) - 1;
}

int occurlist_bs(int * occurlist, int cindex)
{
	return ceiling_binary_search(occurlist + 1, occurlist[0], cindex) + 1;
}

int occurlist_first_search(int * occurlist, int cindex)
{
	int i = 1;
	for ( ; i <= occurlist[0]; i++)
		if (cindex <= occurlist[i])
			break;
	return i;
}

int occurlist_last_search(int * occurlist, int cindex)
{
	int i = occurlist[0];
	for ( ; i > 0; i--)
		if (cindex > occurlist[i])
			break;
	return i + 1;
}

void occurlist_add(Formula * formula, int lit, int cindex, int (*finder)(int *, int))
{
	int * ol = formula->occurlists[lit];
	int index = finder(ol, cindex);

	if (ol[index] == cindex) return;

	// adding the cindex to the increasing indices
	for (int i = ol[0]; i >= index; i--)
		ol[i + 1] = ol[i];
	ol[index] = cindex;
	ol[0]++;
}

void occurlist_lit_remove(Formula * formula, int lit, int cindex, int (*finder)(int *, int))
{
	int * ol = formula->occurlists[lit];
	int index = finder(ol, cindex);
	if (ol[index] != cindex) return;

	// removing cindex from increasing indices
	for ( ; index < ol[0]; index++)
		ol[index] = ol[index + 1];
	ol[0]--;
}

void occurlist_lit_remove_all(Formula * formula, int lit)
{
	secure_free(formula->occurlists[lit]);
	formula->occurlists[lit] = NULL;
}

int occurlist_has_content(Formula * formula, int lit)
{
	return formula->occurlists[lit] != NULL && formula->occurlists[lit][0] != 0;
}

unsigned int occurlist_var_state(Formula * formula, int var)
{
	return
		(occurlist_has_content(formula, -var) << 1) |
		occurlist_has_content(formula, var);
}

int * new_occurlist(int n_clauses)
{
	int * ol = malloc((n_clauses + 1) * sizeof * ol);
	ol[0] = 0;
	memset(ol, -1, n_clauses * sizeof * ol);
	return ol;
}

Formula * new_formula(int n_vars, int n_clauses)
{
	Formula * f = malloc(sizeof * f);

	f->n_vars = n_vars;
	f->n_clauses = n_clauses;
	f->n_clauses_init = n_clauses;
	f->n_lits = n_clauses * (EXPLPC + 1);

	// literals ranging from -var to var, 0 unused
	f->occurlists = malloc((2 * n_vars + 1) * sizeof * f->occurlists);
	// 0-centered
	f->occurlists += n_vars;
	for (int var = 1; var <= n_vars; var++) {
		f->occurlists[var] = new_occurlist(n_clauses);
		f->occurlists[-var] = new_occurlist(n_clauses);
	}
	f->occurlists[0] = NULL;
	// plus 1 is for algorithm's efficiency
	f->off_clauses = malloc((n_clauses + 1) * sizeof * f->off_clauses);
	f->lits = malloc(f->n_lits * sizeof * f->lits);

	f->i_lit = 0;
	f->assignments = calloc(n_vars, sizeof * f->assignments);
	// 1-indexed
	f->assignments--;

	return f;
}

int * memory_copy(int * src, int n)
{
	if (src == NULL) return NULL;

	int size = n * sizeof * src;
	int * res = malloc(size);
	memcpy(res, src, size);
	return res;
}

int * copy_occurlist(int * ol)
{
	return ol == NULL ? NULL : memory_copy(ol, ol[0] + 1);
}

// copied occurlists are not to be extended
int ** copy_occurlists(Formula * formula)
{
	int ** ols = malloc((2 * formula->n_vars + 1) * sizeof * ols);
	ols += formula->n_vars;
	for (int var = 1; var <= formula->n_vars; var++) {
		ols[var] = copy_occurlist(formula->occurlists[var]);
		ols[-var] = copy_occurlist(formula->occurlists[-var]);
	}
	ols[0] = NULL;

	return ols;
}

int * copy_off_clauses(Formula * formula)
{
	return memory_copy(formula->off_clauses, formula->n_clauses_init + 1);
}

int * copy_lits(Formula * formula)
{
	return memory_copy(formula->lits, formula->n_lits);
}

int * copy_assignments(Formula * formula)
{
	int * assignments = memory_copy(formula->assignments + 1, formula->n_vars);
	return assignments - 1;
}

Formula * copy_formula(Formula * formula)
{
	Formula * f = malloc(sizeof * f);

	f->n_vars = formula->n_vars;
	f->n_clauses = formula->n_clauses;
	f->n_clauses_init = formula->n_clauses_init;
	f->n_lits = formula->n_lits;

	// copy the occurlist
	f->occurlists = copy_occurlists(formula);
	f->off_clauses = copy_off_clauses(formula);
	f->lits = copy_lits(formula);

	f->i_lit = formula->i_lit;
	f->assignments = copy_assignments(formula);

	return f;
}

Formula * del_formula(Formula * formula)
{
	for (int var = 1; var < formula->n_vars; var++) {
		occurlist_lit_remove_all(formula, var);
		occurlist_lit_remove_all(formula, -var);
	}

	free(formula->occurlists - formula->n_vars);
	free(formula->off_clauses);
	free(formula->lits);
	free(formula->assignments + 1);

	free(formula);
	return NULL;
}

int * clause_get(Formula * formula, int i)
{
	if (i >= formula->n_clauses_init) return NULL;
	int * clause = formula->lits + formula->off_clauses[i];
	if (clause[0] == CL_NONE) return NULL;
	return clause;
}

void clause_remove(Formula * formula, int clause_i, int (*finder)(int *, int))
{
	int * clause = clause_get(formula, clause_i);
	if (clause == NULL) return;

	for (int i = 1; i <= clause[0]; i++) {
		occurlist_lit_remove(formula, clause[i], clause_i, finder);
	}

	clause[0] = CL_NONE;
	formula->n_clauses--;
}

void lits_add(Formula * formula, int lit, int cindex)
{
	if (formula->i_lit >= formula->n_lits) {
		formula->n_lits *= 2;
		formula->lits = realloc(formula->lits, formula->n_lits * sizeof * formula->lits);
	}

	occurlist_add(formula, lit, cindex, occurlist_last_search);
	formula->lits[formula->i_lit++] = lit;
}

void lits_remove(Formula * formula, int lit, int clause_i, int (*finder)(int *, int))
{
	int * clause = clause_get(formula, clause_i);
	if (clause == NULL) return;

	int shift = 0;
	for (int i = 1; i <= clause[0]; i++) {
		clause[i - shift] = clause[i];
		if (clause[i - shift] == lit) {
			shift++;
		}
	}
	clause[0] -= shift;

	occurlist_lit_remove(formula, lit, clause_i, finder);
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

	while (i_clause < result->n_clauses_init && fgets(buffer, BUFFERSIZE, fp) != NULL)
	{
		if (*buffer == 'c') {
			// a comment
		}
		else {
			// a clause
			int i_lit = 0;
			int lit;
			char * token = strtok(buffer, " ");

			int size_index_offset = result->i_lit++;
			while (token != NULL)
			{
				lit = atoi(token);
				if (lit == 0) break;

				lits_add(result, lit, i_clause);
				token = strtok(NULL, " ");
				i_lit++;
			}

			result->off_clauses[i_clause + 1] = result->i_lit;
			result->lits[size_index_offset] = i_lit;

			i_clause++;
		}
	}

	if (i_clause != result->n_clauses_init) {
		fprintf(stderr, "%d/%d clauses are missing.\n", result->n_clauses_init - i_clause, result->n_clauses_init);
		return del_formula(result);
	}

	if (ferror(fp)) {
		perror("Error reading file.");
		return del_formula(result);
	}

	return result;
}

void unit_propagate(Formula * formula, int unit)
{
	for (int i = formula->occurlists[unit][0]; i > 0; i--)
		clause_remove(formula, formula->occurlists[unit][i], occurlist_last_search);
	occurlist_lit_remove_all(formula, unit);

	while (formula->occurlists[-unit][0])
		lits_remove(formula, -unit, formula->occurlists[-unit][1], occurlist_bs);
	occurlist_lit_remove_all(formula, -unit);

	formula->assignments[abs(unit)] = sign(unit);
}

// since unit propagation may introduce new unit clauses, this repeats itself until no change
int empty_clause_and_unit_propagate(Formula * formula)
{
	int last_change = 0;
	int bypass = 1;

	int i = 0;

	while (formula->n_clauses != 0) {
		for (i = 0; i < formula->n_clauses_init; i++) {
			int * clause = clause_get(formula, i);
			if (clause != NULL) {
				switch (clause[0])
				{
					case 0: return 0;
					case 1:
						unit_propagate(formula, clause[1]);
						last_change = i;
						bypass = 1;
						continue;
				}
			}

			if (!bypass && i >= last_change) return 1;
		}
		bypass = 0;
	}
	return 1;
}

int get_pure(Formula * formula, int var)
{
	switch (occurlist_var_state(formula, var)) {
		case 0b01:
			return var;
		case 0b10:
			return -var;
	}

	return 0;
}

void pure_variable_propagate(Formula * formula, int pure)
{
	for (int i = formula->occurlists[pure][0]; i > 0; i--) {
		clause_remove(formula, formula->occurlists[pure][i], occurlist_last_search);
	}

	occurlist_lit_remove_all(formula, pure);
	formula->assignments[abs(pure)] = sign(pure);
}

// since pure literal propagations may introduce new ones, this repeats itself until no change
void pure_variable_assignment(Formula * formula)
{
	int retry_until = 0;
	int var = 1;

	do for (var = 1; var < formula->n_vars && var != retry_until; var++) {
		int pure = get_pure(formula, var);
		if (pure == 0) continue;

		retry_until = var;
		pure_variable_propagate(formula, pure);
	} while (retry_until != 0 && var != retry_until);
	// retry_until == 0 means it was never set, so there were no pures inside, no need to retry
}

Formula * dpll(Formula *);

Formula * dpll_with_unit(Formula * formula, int unit)
{
	unit_propagate(formula, unit);
	return dpll(formula);
}

int unbiased_random(int n)
{
	int r;
	do r = rand();
	while (r >= RAND_MAX / n * n);
	return r % n;
}

int * choices;

void init_random(Formula * formula)
{
	srand((unsigned int) time(NULL));
	choices = malloc(formula->n_vars * sizeof * choices);
}

void fin_random(void)
{
	free(choices);
}

int choose_var_rand(Formula * formula)
{
	int size_choices = 0;
	for (int lit = 1; lit <= formula->n_vars; lit++)
		if (occurlist_has_content(formula, lit))
			choices[size_choices++] = lit;

	return size_choices == 0 ? 0 : choices[unbiased_random(size_choices)];
}

int choose_var_first(Formula * formula)
{
	for (int var = 1; var <= formula->n_vars; var++) {
		if (occurlist_has_content(formula, var)) return var;
		// if (occurlist_has_content(formula, -var)) return -var;
		// no need for this, as the pure variable assignment would catch it
	}

	return 0;
}

int consistent(Formula * formula)
{
	return formula->n_clauses == 0;
}

void print_clauses(Formula * formula)
{
	puts("======= CLAUSES =======");
	for (int i = 0; i < formula->n_clauses_init; i++)
	{
		int * clause = clause_get(formula, i);
		if (clause == NULL) continue;
		printf("%d > ", i);
		for (int j = 1; j <= clause[0]; j++) {
			printf("%d ", clause[j]);
		}
		putchar(10);
	}
	puts("======= CLAUSES =======");
}

void print_occurlists(Formula * formula)
{
	puts("======= OCCURLS =======");
	for (int var = 1; var <= formula->n_vars; var++) {
		for (int sign = -1; sign <= 1; sign += 2) {
			int lit = var * sign;
			int * ol = formula->occurlists[lit];
			if (ol == NULL || ol[0] == 0) continue;
			printf("%d > ", lit);
			for (int i = 0; i <= ol[0]; i++) {
				printf("%d ", ol[i]);
			}
			putchar(10);
		}
	}
	puts("======= OCCURLS =======");
}

Formula * dpll(Formula * formula)
{
	if (consistent(formula)) return formula;
	if (empty_clause_and_unit_propagate(formula) == 0)
		return del_formula(formula);
	if (consistent(formula)) return formula;
	pure_variable_assignment(formula);
	if (consistent(formula)) return formula;

	// choose a variable and recurse and recurse with its both modalities
	// make a copy for first try, use the current one for the other if it comes to that
	int var = choose_var_first(formula);
	if (var == 0) {
		printf("%d but no vars\n", formula->n_clauses);
		print_clauses(formula);
		print_occurlists(formula);
		return formula;
	}

	Formula * exhibitA = dpll_with_unit(copy_formula(formula), var);
	if (exhibitA != NULL)
		return exhibitA;

	return dpll_with_unit(formula, -var);
}

void print_formula(Formula * formula)
{
	for (int var = 1; var <= formula->n_vars; var++) {
		printf("%d ", formula->assignments[var] * var);
	}
	putchar('\n');
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
		fputs("Formula is NULL\n", stderr);
		return -1;
	}

	init_random(formula);
	formula = dpll(formula);
	fin_random();

	if (formula == NULL) {
		puts("Unsatisfiable.");
	}
	else {
		puts("Satisfiable!");
		print_formula(formula);
	}

	return 0;
}
