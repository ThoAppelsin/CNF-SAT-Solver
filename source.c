#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define BUFFERSIZE 1024
#define EXPLPC 4

#define sign(x) ((x) >= 0 ? 1 : -1)

#define OL_START_POS -1
#define OL_LEN -2

typedef
struct Formula_tag
{
	int n_vars;			// variable count, constant during dpll
	int n_clauses;		// clause count, decreases during dpll
	int n_lits;			// literal count, constant during dpll
	int ** occurlists;		// 1-indexed list (n_vars) of arrays of clause indices
								// 0-indexed increasing arrays
								// sign indicates negative or positive occurrence
								// -1th index is the start of positives
								// -2th index is the number of all positives and negatives
	int * off_clauses;		// array (n_clauses + 1) of increasing numbers, starting with zero
	int * lits;				// list (n_lits) of literals for the whole formula
								// zero implies absence of literal, n_vars + 1 is a clause boundary
	int * clause_lengths;	// list of (n_clauses) many clause length values
	int i_lit;
	int * assignments;		// 1-indexed list of (n_vars) of +/- 1s
} Formula;

int binary_search(int * arr, int len, int x)
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

int occurlist_bs(int * occurlist, int cindex)
{
	return binary_search(occurlist + 1, occurlist[0], cindex) + 1;
}

void occurlist_add(Formula * formula, int lit, int cindex)
{
	int var = abs(lit);
	int * ol = formula->occurlists[var];
	int index = occurlist_abs_bs(ol, cindex);

	if (abs(ol[index]) == cindex) return;

	// adding the cindex to the increasing indices
	for (int i = ol[0]; i >= index; i--)
		ol[i + 1] = ol[i];
	ol[index] = cindex * sign(lit);
	ol[0]++;
}

void occurlist_lit_remove(Formula * formula, int var, int cindex)
{
	int * ol = formula->occurlists[var];
	int index = occurlist_bs(ol, cindex);
	if (ol[index] != cindex) return;

	// removing cindex from increasing indices
	for ( ; index < ol[0]; index++)
		ol[index] = ol[index + 1];
	ol[0]--;
}

unsigned int occurlist_var_state(Formula * formula, int var)
{
	unsigned int state = 0b00;
	int * ol = formula->occurlists[var];

	for (int i = 1; i <= ol[0]; i++) {
		if (formula->lits[*occur] > 0)
			state |= 0b01;
		else	// occurlist is supposed to point existent literals, no absent/zero literals
			state |= 0b10;
		if (state & 0b11) return state;
		occur++;
	}

	return state;
}

Formula * new_formula(int n_vars, int n_clauses)
{
	Formula * f = malloc(sizeof * f);

	f->n_vars = n_vars;
	f->n_clauses = n_clauses;
	f->n_lits = n_clauses * EXPLPC;

	// variable names starting with 1
	f->occurlist = malloc(n_vars * sizeof * f->occurlist);
	f->occurlist--;
	for (int var = 1; var <= f->n_vars; var++) {
		f->occurlist[var] = calloc((n_clauses + 1) * sizeof * f->occurlist[var]);
	}
	// plus 1 is for algorithm's efficiency
	f->off_clauses = malloc((n_clauses + 1) * sizeof * f->off_clauses);
	f->lits = malloc(f->n_lits * sizeof * f->lits);
	f->clause_lengths = calloc(n_clauses, sizeof * f->clause_lengths);

	f->i_lit = 0;
	f->assignments = calloc(n_vars, sizeof * f->assignments);
	f->assignments--;

	return f;
}

int * memory_copy(int * src, int n)
{
	int size = n * sizeof * src;
	int * res = malloc(size);
	memcpy(res, src, size);
	return res;
}

int * copy_occur(int * occur)
{
	return memory_copy(occur, occur[0] + 1);
}

int ** copy_occurlist(Formula * formula)
{
	int ** ol = malloc(formula->n_vars * sizeof * ol);
	ol--;
	for (int var = 1; var <= formula->n_vars; var++)
		ol[var] = copy_occur(formula->occurlist[var]);

	return ol;
}

int * copy_off_clauses(Formula * formula)
{
	return memory_copy(formula->off_clauses, formula->n_clauses + 1);
}

int * copy_lits(Formula * formula)
{
	return memory_copy(formula->lits, formula->n_lits);
}

int * copy_clause_lengths(Formula * formula)
{
	return memory_copy(formula->clause_lengths, formula->n_clauses);
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
	f->n_lits = formula->n_lits;

	// copy the occurlist
	f->occurlist = copy_occurlist(formula);
	f->off_clauses = copy_off_clauses(formula);
	f->lits = copy_lits(formula);
	f->clause_lengths = copy_clause_lengths(formula);

	f->i_lit = formula->i_lit;
	f->assignments = copy_assignments(formula);

	return f;
}

Formula * del_formula(Formula * formula)
{
	for (int var = 1; var < formula->n_vars; var++)
		free(formula->occurlist[var]);

	free(formula->occurlist + 1);
	free(formula->off_clauses);
	free(formula->lits);
	free(formula->clause_lengths);
	free(formula->assignments + 1);

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

int clause_get_lit(Formula * formula, int clause_i, int n)
{
	int * clause = clause_get(formula, clause_i);
	if (n > formula->clause_lengths[clause_i]) return 0;

	for (int i = 0; ; i++)
		if (clause[i] != 0)
			if (--n == 0)
				return clause[i];

	return 0;
}

void clause_remove(Formula * formula, int clause_i)
{
	int * clause = clause_get(formula, clause_i);

	for (int i = 0, c = 0; c < formula->clause_lengths[clause_i]; i++) {
		if (clause[i] != 0) {
			occurlist_lit_remove(formula, formula->off_clauses[clause_i] + i);
			c++;
		}
	}

	clause[0] = formula->n_vars + 1;

	// shifting all the clause offsets and lengths, including the extra final tick for OC
	for (int i = clause_i; ; i++) {
		formula->off_clauses[i] = formula->off_clauses[i + 1];
		if (i == formula->n_clauses - 1) break;
		formula->clause_lengths[i] = formula->clause_lengths[i + 1];
	}

	formula->n_clauses--;
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

void lits_remove(Formula * formula, int offset, int clause_i)
{
	occurlist_lit_remove(formula, offset);
	formula->lits[offset] = 0;
	formula->clause_lengths[clause_i]--;
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
			result->clause_lengths[i_clause] = i_lit;

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

	while (*occur != OL_END) {
		int ci = clause_i_for_offset(formula, *occur);
		if (formula->lits[*occur] == unit) {
			if (ci <= clause_i)
				clause_i--;
			clause_remove(formula, ci);
		}
		else {
			lits_remove(formula, *occur, ci);
		}
	}

	occurlist_var_remove(formula, var);
	formula->assignments[var] = (unit >= 0) ? 1 : -1;

	return clause_i;
}

// since unit propagation may introduce new unit clauses, this repeats itself until no change
int empty_clause_and_unit_propagate(Formula * formula)
{
	int retry_last = formula->n_clauses - 1;
	int i = 0;

	while (formula->n_clauses != 0) {
		for (i = 0; i < formula->n_clauses; i++) {
			switch (formula->clause_lengths[i])
			{
				case 0: return 0;
				case 1:
					i = unit_propagate(formula, i, clause_get_lit(formula, i, 1));
					retry_last = (i >= 0) ? i : formula->n_clauses - 1;
					continue;
			}

			if (i == retry_last) return 1;
		}
	}
	return 1;
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

void pure_variable_propagate(Formula * formula, int var)
{
	int * occur = formula->occurlist[var];
	int lit = *occur;
	while (*occur != OL_END)
		clause_remove(formula, clause_i_for_offset(formula, *occur));

	occurlist_var_remove(formula, var);
	formula->assignments[var] = (lit >= 0) ? 1 : -1;
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
		pure_variable_propagate(formula, var);
	} while (retry_until != 0 && var != retry_until);
	// retry_until == 0 means it was never set, so there were no pures inside, no need to retry
}

Formula * dpll(Formula *);

Formula * dpll_with_unit(Formula * formula, int unit)
{
	unit_propagate(formula, 0, unit);
	return dpll(formula);
}

int choose_var_first(Formula * formula)
{
	for (int var = 1; var < formula->n_vars; var++)
		if (formula->occurlist[var] != NULL && formula->occurlist[var][0] != OL_END)
			return var;

	return 0;
}

int consistent(Formula * formula)
{
	return formula->n_clauses == 0;
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

	formula = dpll(formula);
	if (formula == NULL) {
		puts("Unsatisfiable.");
	}
	else {
		puts("Satisfiable!");
		print_formula(formula);
	}

	return 0;
}
