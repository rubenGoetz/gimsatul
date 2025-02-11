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

#define VALID_INTERNAL_LITERAL(LIT) ((LIT) < ring->ruler->size)

#define ABS(LIT) (LIT < 0 ? -LIT : LIT)

#define VALID_EXTERNAL_LITERAL(LIT) ((LIT) && ((LIT) != INT_MIN) && ABS (LIT) <= MAX_VAR)

#define INVALID_REF UINT_MAX

struct gimsatul {
    struct options *options;
    struct ruler *ruler;
    signed char *witness;
    size_t variables, clauses;

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
    set_signal_handlers(solver->ruler);

    solver->ruler->consume_clause_state = 0;
    solver->ruler->consume_clause_buffer = 0;
    solver->ruler->consume_clause_max_size = 0;
    solver->ruler->consume_clause = 0;

    solver->ruler->produce_clause_state = 0;
    solver->ruler->produce_clause = 0;
    solver->ruler->num_conflicts_at_last_import = 0;

    solver->ruler_initialized = true;
}

gimsatul *gimsatul_init (int variables, int clauses) {
    // Adapted from gimsatul.c/main()
    // printf(">> inside gimsatul_init\n");
    struct gimsatul *solver = (struct gimsatul*) calloc(1, sizeof(struct gimsatul));
    solver->options = (struct options*) calloc(1, sizeof(struct options));
    initialize_options(solver->options);
    solver->variables = variables;
    solver->clauses = clauses;
    solver->witness = NULL;

    solver->marked = allocate_and_clear_block (solver->variables);
    solver->clause = (struct unsigneds*) calloc(1, sizeof(struct unsigneds));
    solver->trivial = false;

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

const unsigned gimsatul_import_literal(struct ring * ring, int elit) {
  // printf(">> inside gimsatul_import_literal\n");
  unsigned idx = abs (elit) - 1;
  assert (idx < (unsigned) ring->ruler->size);
  signed char sign = (elit < 0) ? -1 : 1;
  //signed char mark = solver->marked[idx];
  return (const unsigned) 2 * idx + (sign < 0);
}

bool gimsatul_importing_redundant_clauses (struct ring * ring) 
{
  // printf(">> inside gimsatul_importing_redundant_clauses\n");
  if (ring->produce_clause == 0) return false;
  if (ring->level != 0) return false;
  unsigned long conflicts = SEARCH_CONFLICTS;
  if (conflicts == ring->num_conflicts_at_last_import) return false;
  return true;
}

void gimsatul_import_redundant_clauses (struct ring * ring) 
{
  // printf(">> inside gimsatul_import_redundant_clauses\n");
  int *buffer = 0;
  int size = 0;
  int glue = 0;
  ring->num_conflicts_at_last_import = SEARCH_CONFLICTS;
  // TODO: put in ruler
  struct unsigneds *clause = (struct unsigneds*) calloc(1, sizeof(struct unsigneds));

  while (true) {
    ring->produce_clause (ring->produce_clause_state, &buffer, &size, &glue);

    //printf("KISSAT TRY_LEARN size=%i\n", size);

    if (size <= 0 || buffer == 0) {
      break; // No more clauses
    }

    // Literal flags to possibly check against:
    // bool eliminate:1; /* set by kissat_mark_removed_literal */
    //!bool eliminated:1; /*do not import*/
    // bool fixed:1; /*can be handled explicitly*/
    // bool subsume:1; /* set by kissat_mark_added_literal, also when importing the clause */
    // bool sweep:1; /*could be fine*/
    // bool transitive:1; /*seems to be used nowhere*/

    // Analyze each of the literals
    bool okToImport = true;
    unsigned effectiveSize = 0;
    for (unsigned i = 0; i < (unsigned)size; i++) {
      int elit = buffer[i];
      if (!VALID_EXTERNAL_LITERAL (elit)) {
	      ring->r_ed++;
        okToImport = false;
        break;
      }
      const unsigned ilit = gimsatul_import_literal (ring, elit);
      if (!VALID_INTERNAL_LITERAL (ilit)) {
	      ring->r_ed++;
        okToImport = false;
        break;
      }
      const unsigned idx = IDX (ilit);
      // TODO: check Flags
      /*
      flags *flags = FLAGS (idx);
      if (flags->fixed) {
        const value value = gimsatul_fixed (solver, ilit);
        if (value > 0) {
          // Literal is fixed as positive: drop entire clause
          solver->r_fx++;
          okToImport = false;
          break;
        } else if (value < 0) {
          // Literal is fixed as negated: drop this literal
          buffer[i] = 0;
        } else {
          // Fixed, but neither positive nor negated? Drop clause to be safe
          solver->r_fx++;
          okToImport = false;
          break;
        }
      } else if (!flags->active || flags->eliminated) {
        // Literal in an invalid state for importing this clause
        okToImport = false;

        if (!flags->active) solver->r_ia++;
        if (flags->eliminate) solver->r_ee++;
        if (flags->eliminated) solver->r_ed++;
        if (flags->subsume) solver->r_ss++;
        if (flags->sweep) solver->r_sw++;
        if (flags->transitive) solver->r_tr++;

        break;
      } else {
        // This literal is fine
        effectiveSize++;
      }*/
      // Replacing flag logic
      if (ring->ruler->eliminate[idx]) {
        okToImport = false;
        ring->r_ed++;
      } else if (!(ring->inactive[idx] && !ring->values[idx])) {
        okToImport = false;
        ring->r_fx++; // correct?
      } else 
        effectiveSize++;
    }

    // Drop clause, or no valid literals?
    if (!okToImport || effectiveSize == 0) {
      ring->num_discarded_external_clauses++;
      continue;
    }

    if (effectiveSize == 1) {
      // Unit clause!

      // Get literal
      unsigned i = 0; while (buffer[i] == 0) i++;
      const unsigned lit = gimsatul_import_literal (ring, buffer[i]);
      assert (VALID_INTERNAL_LITERAL (lit));

      // Learn unit clause
      //printf("GIMSATUL LEARN %i\n", lit);
      // Import shared unit while avoiding its re-export
      //gimsatul_learned_unit_from_import (ring, lit);  // TODO: implement
      assign_ruler_unit (ring->ruler, lit);
      ring->num_imported_external_clauses++;
      continue;
    }

    // Larger clause of size >= 2

    /*if (effectiveSize > CAPACITY_STACK (solver->clause)) {
      // Clause is too large
      solver->r_tl++;
      solver->num_discarded_external_clauses++;
      continue;
    }*/

    // Write clause into internal stack
    assert (EMPTY (*(clause)));
    //printf("KISSAT LEARN");
    for (unsigned i = 0; i < (unsigned)size; i++) {
      if (buffer[i] == 0) continue;
      const unsigned lit = gimsatul_import_literal (ring, buffer[i]);
      assert (VALID_INTERNAL_LITERAL (lit));
      PUSH (*(clause), lit);
      //printf(" %i", lit);
    }
    //printf("\n");
    assert (SIZE (*(clause)) == effectiveSize);

    // Learn clause, re-export iff the clause was just shortened
    // (i.e., block re-export iff the clause is imported without changes)
    // const unsigned int ref = gimsatul_new_redundant_clause_from_import (ring, glue);   // TODO: implement
    if (effectiveSize == 2) {
      struct watch *c = new_local_binary_clause(ring, true, *(clause->begin), *(clause->end));
      import_binary_from_mallob (ring, c);
    }
    else {
      struct clause *c = new_large_clause (size, clause->begin, false, 0);
      import_large_clause_from_mallob (ring, c);
    }
    

    /*if (ref != INVALID_REF) {
      // Valid reference => Long clause (size>2) 
      assert (effectiveSize > 2);
      clause *c = kissat_dereference_clause (solver, ref);
      c->used = 1 + (glue <= GET_OPTION (tier2));
    }*/

    // Clear internal stack for the next learnt clause
    CLEAR (*(clause));
    ring->num_imported_external_clauses++;
  }

  free(clause);
  //printf("KISSAT next import @ %lu conflicts\n", solver->num_conflicts_at_last_import);
}

// Sets a function to be called whenever kissat learns a clause no longer than the specified max. size.
// The function is called with the provided state and the size and glue value of the learnt clause.
// The clause itself is stored in the provided buffer before the function is called.
void gimsatul_set_clause_export_callback (gimsatul * solver, void *state, int **buffer, unsigned max_size, void (*consume) (void *state, int size, int glue, int ring_id)){
    // printf(">> inside gimsatul_set_clause_export_callback\n");
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
    // printf(">> inside gimsatul_set_clause_import_callback\n");
    if (!solver->ruler_initialized) create_ruler(solver);
    solver->ruler->produce_clause_state = state;
    solver->ruler->produce_clause = produce;
}

// Basic "external" statistics struct with some interesting properties of kissat's search.
// Get the statistics of kissat's current search. Not thread-safe, but only reading, i.e.,
// may (rarely) return improper values.
// struct gimsatul_statistics gimsatul_get_statistics (gimsatul * solver){}

// Provides to kissat an array of variable phase values. lookup[i] corresponds to external variable i
// and should be 1, -1, or 0. Kissat may lookup this value for a variable and use the sign to decide
// on the variable's initial phase. The array must be valid during the entire search procedure.
void gimsatul_set_initial_variable_phases (gimsatul * solver, signed char *lookup, int size){}
