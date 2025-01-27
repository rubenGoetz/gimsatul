#ifndef _gimsatul_h_INCLUDED
#define _gimsatul_h_INCLUDED

typedef struct gimsatul gimsatul;

// Default (partial) IPASIR interface.

const char *gimsatul_signature (void);
gimsatul *gimsatul_init (int variables, int clauses);
void gimsatul_add (gimsatul *solver, int signed_lit);
int gimsatul_solve (gimsatul *solver);
int gimsatul_value (gimsatul *solver, int lit);
void gimsatul_release (gimsatul *solver);
void gimsatul_set_terminate (gimsatul *solver, void *state,
                             int (*terminate) (void *state));

// Additional API functions.

void gimsatul_terminate (gimsatul *solver);
void gimsatul_reserve (gimsatul *solver, int max_var);

const char *gimsatul_id (void);
const char *gimsatul_version (void);
const char *gimsatul_compiler (void);

const char **gimsatul_copyright (void);
void gimsatul_build (const char *line_prefix);
void gimsatul_banner (const char *line_prefix, const char *name_of_app);

int gimsatul_get_option (gimsatul *solver, const char *name);
int gimsatul_set_option (gimsatul *solver, const char *name, int new_value);

int gimsatul_has_configuration (const char *name);
int gimsatul_set_configuration (gimsatul *solver, const char *name);

void gimsatul_set_conflict_limit (gimsatul *solver, unsigned);
void gimsatul_set_decision_limit (gimsatul *solver, unsigned);

void gimsatul_print_statistics (gimsatul *solver);


// Adapted from kissat.h
// *** API for Mallob ***

// Sets a function to be called whenever kissat learns a clause no longer than the specified max. size.
// The function is called with the provided state and the size and glue value of the learnt clause.
// The clause itself is stored in the provided buffer before the function is called.
void gimsatul_set_clause_export_callback (gimsatul * solver, void *state, int** buffer, unsigned max_size, void (*consume) (void *state, int size, int glue, int ring_id));

// Sets a function which kissat may call to import a clause from another solver. The function is called
// with the provided state and expects a literal buffer (or zero), the clause size, and the glue value as out parameters.
// If no clause is available, the function must return clause == 0.
void gimsatul_set_clause_import_callback (gimsatul * solver, void *state, void (*produce) (void *state, int **clause, int *size, int *glue));

// Basic "external" statistics struct with some interesting properties of kissat's search.
struct gimsatul_statistics {unsigned long propagations; unsigned long decisions; unsigned long conflicts; unsigned long restarts;
    unsigned long imported; unsigned long discarded; unsigned long r_ee,r_ed,r_pb,r_ss,r_sw,r_tr,r_fx,r_ia,r_tl;};
// Get the statistics of kissat's current search. Not thread-safe, but only reading, i.e.,
// may (rarely) return improper values.
struct gimsatul_statistics gimsatul_get_statistics (gimsatul * solver);

// Provides to kissat an array of variable phase values. lookup[i] corresponds to external variable i
// and should be 1, -1, or 0. Kissat may lookup this value for a variable and use the sign to decide
// on the variable's initial phase. The array must be valid during the entire search procedure.
void gimsatul_set_initial_variable_phases (gimsatul * solver, signed char *lookup, int size);

#endif