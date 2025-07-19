#include "libgimsatul.h"
#include "ruler.h"
#include "build.h"
#include "witness.h"
#include "solve.h"
#include "options.h"
#include "catch.h"
#include "simplify.h"
#include "clone.h"
#include "detach.h"
#include "parse.h"
#include "geatures.h"
#include "message.h"
#include "options.h"
#include "parse.h"
#include "statistics.h"
#include "macros.h"
#include "import.h"

#include "options.c"

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

struct gimsatul {
    struct options *options;
    struct ruler *ruler;
    signed char *witness;
    size_t variables, clauses;
    char **initial_phases_pointer;

    // meta information needed for gimsatul_add()
    signed char *marked;
    struct unsigneds *clause;
    bool trivial;

    // indicates whether ruler was created already
    bool ruler_initialized;
};

// const char *gimsatul_signature (void) { return "gimsatul-" VERSION; }

// Default (partial) IPASIR interface.

void create_ruler(struct gimsatul* solver) {
    // printf(">> inside create_ruler\n");
    if (solver->options->threads <= 0) solver->options->threads = 1;
    solver->ruler = new_ruler(solver->variables, solver->options);
    //set_signal_handlers(solver->ruler);

    solver->ruler->consume_clause_state = 0;
    solver->ruler->consume_clause_buffer = 0;
    solver->ruler->consume_clause_max_size = 0;
    solver->ruler->consume_clause = 0;

    solver->ruler->produce_clause_state = 0;
    solver->ruler->produce_clause = 0;
    solver->ruler->num_conflicts_at_last_import = 0;

    solver->ruler->initial_phases_pointer = solver->initial_phases_pointer;

    solver->ruler_initialized = true;
}

gimsatul *gimsatul_init (int variables, int clauses, char **phases) {
    // Adapted from gimsatul.c/main()
    struct gimsatul *solver = (struct gimsatul*) calloc(1, sizeof(struct gimsatul));
    solver->options = (struct options*) calloc(1, sizeof(struct options));
    initialize_options(solver->options);
    solver->variables = variables;
    solver->clauses = clauses;
    solver->witness = NULL;

    solver->marked = allocate_and_clear_block (solver->variables);
    solver->clause = (struct unsigneds*) calloc(1, sizeof(struct unsigneds));
    solver->trivial = false;

    solver->initial_phases_pointer = phases;

    return solver;
}

void gimsatul_add (gimsatul *solver, int signed_lit) {
    //printf(">> inside gimsatul_add\n");
    if (!solver->ruler_initialized) create_ruler(solver);
    // Adapted from parse.c/parse_dimacs_body()
    if (signed_lit) {
        unsigned idx = abs (signed_lit) - 1;
        assert (idx < (unsigned) solver->variables);
        signed char sign = (signed_lit < 0) ? -1 : 1;
        signed char mark = solver->marked[idx];
        unsigned unsigned_lit = 2 * idx + (sign < 0);
#ifndef NDEBUG
        PUSH (*(solver->ruler->original), unsigned_lit);
#endif
        if (mark == -sign) {
            ROG ("skipping trivial clause");
            solver->trivial = true;
        } else if (!mark) {
            PUSH (*(solver->clause), unsigned_lit);
            solver->marked[idx] = sign;
        } else
            assert (mark == sign);
    } else {        // if clause finished
#ifndef NDEBUG
        PUSH (*(solver->ruler->original), INVALID);
#endif
        unsigned *literals = solver->clause->begin;
        if (!solver->ruler->inconsistent && !solver->trivial) {
            const size_t size = SIZE (*(solver->clause));
            assert (size <= solver->ruler->size);
            if (!size) {
                assert (!solver->ruler->inconsistent);
                very_verbose (0, "%s", "found empty original clause");
                solver->ruler->inconsistent = true;
            } else if (size == 1) {
                const unsigned unit = *(solver->clause->begin);
                const signed char value = solver->ruler->values[unit];
                if (value < 0) {
                    assert (!solver->ruler->inconsistent);
                    very_verbose (0, "found inconsistent unit");
                    solver->ruler->inconsistent = true;
                    trace_add_empty (&(solver->ruler->trace));
                } else if (!value)
                    assign_ruler_unit (solver->ruler, unit);
            } else if (size == 2)
                new_ruler_binary_clause (solver->ruler, literals[0], literals[1]);
            else {
                struct clause *large_clause =
                        new_large_clause (size, literals, false, 0);
                // ROGCLAUSE (large_clause, "new");
                PUSH (solver->ruler->clauses, large_clause);
            }
        } else
            solver->trivial = false;
        for (all_elements_on_stack (unsigned, unsigned_lit, *(solver->clause)))
            solver->marked[IDX (unsigned_lit)] = 0;
        CLEAR (*(solver->clause));
    }
}

int gimsatul_solve (gimsatul *solver) {
    // printf(">> inside gimsatul_solve\n");
    if (!solver->ruler_initialized) create_ruler(solver);
    simplify_ruler(solver->ruler);
    clone_rings(solver->ruler);
    struct ring *winner = solve_rings(solver->ruler);
    int res = winner ? winner->status : 0;
    if (res == 10) {
        signed char *witness = extend_witness(winner);
        solver->witness = witness;
    }
    return res;
}

int gimsatul_value (gimsatul *solver, int lit) {
    return lit * solver->witness[lit];
}

void gimsatul_release (gimsatul *solver) {
    if (solver->ruler_initialized) detach_and_delete_rings(solver->ruler);
    if (solver->ruler_initialized) delete_ruler(solver->ruler);
    free(solver->marked);
    free(solver);
}

int gimsatul_set_option (gimsatul *solver, const char *name, int new_value) {
//void parse_options (int argc, char **argv, struct options *opts) {
//initialize_options (opts);

#ifndef QUIET
    const char *quiet_opt = 0;
    const char *verbose_opt = 0;
#endif
    //for (int i = 1; i != argc; i++) {
    //const char *opt = argv[i], *arg; Syntax?
    const char *opt = name, *arg;
    struct options *opts = solver->options;
    if (!strcmp (opt, "-a"))
      opts->binary = false;
    else if (!strcmp (opt, "-f"))
      opts->force = true;
    else if (!strcmp (opt, "-h") || !strcmp (opt, "--help") ||
             !strcmp (opt, "--full")) { /* hopefully no help needed */}
    else if (!strcmp (opt, "-i") || !strcmp (opt, "--id")) {
      print_id ();
      return (0);
    } else if (!strcmp (opt, "-l") || !strcmp (opt, "--log") ||
               !strcmp (opt, "logging"))
#ifdef LOGGING
      verbosity = INT_MAX;
#else
      return 1;
      // die ("invalid option '%s' (compiled without logging support)", opt);
#endif
    else if (!strcmp (opt, "-n"))
      opts->witness = false;
    else if (!strcmp (opt, "-O"))
      opts->optimize = 1;
    else if (opt[0] == '-' && opt[1] == 'O') {
      arg = opt + 2;
      if (!is_positive_number_string (arg) ||
          sscanf (arg, "%u", &opts->optimize) != 1)
        return 1;
        // die ("invalid '-O' option '%s'", opt);
    } else if (!strcmp (opt, "-r") || !strcmp (opt, "--resources"))
      opts->summarize = true;
    else if (!strcmp (opt, "-q") || !strcmp (opt, "--quiet"))
#ifdef QUIET
      return 1;
      // die ("configured with '--quiet' (forces '%s)", opt);
#else
    {
      if (quiet_opt)
        return 1;
        // die ("two quiet options '%s' and '%s'", quiet_opt, opt);
      if (verbose_opt)
        return 1;
        // die ("quiet option '%s' follows verbose '%s'", opt, verbose_opt);
      quiet_opt = opt;
      verbosity = -1;
    }
#endif
    else if (!strcmp (opt, "-v") || !strcmp (opt, "--verbose"))
#ifdef QUIET
      return 1;
      // die ("configured with '--quiet' (disables '%s')", opt);
#else
    {
      if (quiet_opt)
        return 1;
        // die ("verbose option '%s' follows quiet '%s'", opt, quiet_opt);
      verbose_opt = opt;
      if (verbosity < INT_MAX)
        verbosity++;
    }
#endif
    else if (!strcmp (opt, "-V") || !strcmp (opt, "--version")) {
      print_version ();
      return 0;
    } else if (!strcmp (opt, "conflicts")) {
      if (opts->conflicts >= 0)
        return 1;
        // die ("multiple '--conflicts=%lld' and '%s'", opts->conflicts, opt);
      opts->conflicts = new_value;
      if (opts->conflicts < 0)
        return 1;
        // die ("invalid negative argument in '%s'", opt);
    } else if (!strcmp (opt, "threads")) {
      if (opts->threads)
        return 1;
        // die ("multiple '--threads=%u' and '%s'", opts->threads, opt);
      opts->threads = new_value;
      if (!opts->threads)
        return 1;
        // die ("invalid zero argument in '%s'", opt);
      if (opts->threads > MAX_THREADS)
        return 1;
        // die ("invalid argument in '%s' (maximum %u)", opt, MAX_THREADS);
    } else if (!strcmp (opt, "time")) {
      if (opts->seconds)
        return 1;
        // die ("multiple '--time=%u' and '%s'", opts->seconds, opt);
      opts->seconds = new_value;
      if (!opts->seconds)
        return 1;
        // die ("invalid zero argument in '%s'", opt);
    }
#define OPTION(TYPE, NAME, DEFAULT, MIN, MAX, DESCRIPTION) \
  else if (opt[0] == '-' && opt[1] == '-' && opt[2] == 'n' && \
           opt[3] == 'o' && opt[4] == '-' && \
           parse_option (opt + 5, #NAME)) opts->NAME = false;
    OPTIONS
#undef OPTION
#define OPTION(TYPE, NAME, DEFAULT, MIN, MAX, DESCRIPTION) \
  else if (opt[0] == '-' && opt[1] == '-' && !strcmp (#TYPE, "bool") && \
           parse_option (opt + 2, #NAME)) opts->NAME = true;
    OPTIONS
#undef OPTION
    else if (parse_option_with_value (opts, opt));
    else if (!strcmp (opt, "--embedded")) {print_embedded_options (); return 0;}
    else if (!strcmp (opt, "--range")) {print_option_ranges (); return 0;}
    else if (opt[0] == '-' && opt[1])
        return 1;
        // die ("invalid option '%s' (try '-h')", opt);
    else if (opts->proof.file) 
        return 1;
        // die ("too many arguments");
    else if (opts->dimacs.file) {
      if (!strcmp (opt, "-")) {
        opts->proof.path = "<stdout>";
        opts->proof.file = stdout;
        opts->binary = false;
      } else if (!opts->force && looks_like_dimacs (opt))
        return 1;
        // die ("proof file '%s' looks like a DIMACS file (use '-f')", opt);
      else if (!(opts->proof.file = fopen (opt, "w")))
        return 1;
        // die ("can not open and write to '%s'", opt);
      else {
        opts->proof.path = opt;
        opts->proof.close = true;
      }
    }
    else {
      if (!strcmp (opt, "-")) {
        opts->dimacs.path = "<stdin>";
        opts->dimacs.file = stdin;
      }
      else if (has_suffix (opt, ".bz2") || has_suffix (opt, ".gz") ||
               has_suffix (opt, ".xz"))
        return 1;
        // die ("can not handle compressed file '%s'", opt);
      else {
        opts->dimacs.file = fopen (opt, "r");
        opts->dimacs.close = 1;
      }
      if (!opts->dimacs.file)
        return 1;
        // die ("can not open and read from '%s'", opt);
      opts->dimacs.path = opt;
    }

if (!opts->threads)
    return 1;

#ifndef QUIET
    if (opts->threads <= 10)
        prefix_format = "c%-1u ";
    else if (opts->threads <= 100)
        prefix_format = "c%-2u ";
    else if (opts->threads <= 1000)
        prefix_format = "c%-3u ";
    else if (opts->threads <= 10000)
        prefix_format = "c%-4u ";
    else
        prefix_format = "c%-5u ";
#endif

    if (opts->proof.file == stdout && verbosity >= 0)
        opts->proof.lock = true;

    return 0;
}


// Adapted from kissat.h
// *** API for Mallob ***

// Sets a function to be called whenever kissat learns a clause no longer than the specified max. size.
// The function is called with the provided state and the size and glue value of the learnt clause.
// The clause itself is stored in the provided buffer before the function is called.
void gimsatul_set_clause_export_callback (gimsatul * solver, void *state, int **buffer, unsigned max_size, void (*consume) (void *state, int size, int glue, int ring_id)){
    if (!solver->ruler_initialized) create_ruler(solver);
    solver->ruler->consume_clause_state = state;
    solver->ruler->consume_clause_buffer = buffer;
    solver->ruler->consume_clause_max_size = max_size;
    solver->ruler->consume_clause = consume;
}

// Sets a function which kissat may call to import a clause from another solver. The function is called
// with the provided state and expects a literal buffer (or zero), the clause size, and the glue value as out parameters.
// If no clause is available, the function must return clause == 0.
void gimsatul_set_clause_import_callback (gimsatul * solver, void *state, void (*produce) (void *state, int **clause, int *size, int *glue)){
    if (!solver->ruler_initialized) create_ruler(solver);
    solver->ruler->produce_clause_state = state;
    solver->ruler->produce_clause = produce;
}

// Basic "external" statistics struct with some interesting properties of kissat's search.
// struct gimsatul_statistics {
//   unsigned long propagations;
//   unsigned long decisions;
//   unsigned long conflicts;
//   unsigned long restarts;
//   unsigned long imported;
//   unsigned long discarded;
//   unsigned long r_ee,r_ed,r_pb,r_ss,r_sw,r_tr,r_fx,r_ia,r_tl;
// };
// Get the statistics of kissat's current search. Not thread-safe, but only reading, i.e.,
// may (rarely) return improper values.
struct gimsatul_statistics gimsatul_get_statistics (gimsatul * solver){
  struct ruler *ruler = solver->ruler;
  struct gimsatul_statistics out_stats;

  unsigned acc_propagations = 0;
  unsigned acc_decisions = 0;
  unsigned acc_conflicts = 0;
  unsigned acc_restarts = 0;

  for (all_rings (ring)) {
    acc_propagations += ring->statistics.contexts->propagations;
    acc_decisions += ring->statistics.contexts->decisions;
    acc_conflicts += ring->statistics.contexts->conflicts;
    acc_restarts += ring->statistics.restarts;
  }

  out_stats.propagations = acc_propagations;
  out_stats.decisions = acc_decisions;
  out_stats.conflicts = acc_conflicts;
  out_stats.restarts = acc_restarts;
  out_stats.imported = ruler->num_imported_external_clauses;
  out_stats.discarded = ruler->num_discarded_external_clauses;
  out_stats.r_ee = ruler->r_ee;
  out_stats.r_ee = ruler->r_ee;
  out_stats.r_ed = ruler->r_ed;
  out_stats.r_pb = ruler->r_pb;
  out_stats.r_ss = ruler->r_ss;
  out_stats.r_sw = ruler->r_sw;
  out_stats.r_tr = ruler->r_tr;
  out_stats.r_fx = ruler->r_fx;
  out_stats.r_ia = ruler->r_ia;
  out_stats.r_tl = ruler->r_tl;
  out_stats.r_ilitLvl = ruler->r_ilitLvl;
  out_stats.r_inactive = ruler->r_inactive;
  out_stats.r_bufferFull = ruler->r_bufferFull;

  return out_stats;
}

// Provides to kissat an array of variable phase values. lookup[i] corresponds to external variable i
// and should be 1, -1, or 0. Kissat may lookup this value for a variable and use the sign to decide
// on the variable's initial phase. The array must be valid during the entire search procedure.
void gimsatul_set_initial_variable_phases (gimsatul * solver, signed char *lookup, int size){}

// UTIL
int get_threads(gimsatul *solver) {
  return (int) solver->ruler->options.threads;
}
