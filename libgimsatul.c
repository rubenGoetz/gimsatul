#include "libgimsatul.h"
#include "ruler.h"
#include "build.h"

#include <stdlib.h>

typedef struct gimsatul {
    struct options options;
    struct ruler *ruler;
    signed char *witness;
    size_t variables, clauses;

    // meta information needed for gimsatul_add()
    signed char *marked;
    struct unsigneds clause;
    bool trivial;
};

const char *gimsatul_signature (void) { return "gimsatul-" VERSION; }

// Default (partial) IPASIR interface.

gimsatul *gimsatul_init (size_t variables, size_t clauses) {
    // Adapted from gimsatul.c/main()
    struct gimsatul *solver = (struct gimsatul*) calloc(1, sizeof(struct gimsatul));
    initialize_options(&(solver->options));
    solver->ruler = new_ruler(variables,&(solver->options));
    set_signal_handlers(solver->ruler);
    solver->variables = variables;
    solver->clauses = clauses;
    signed char *witness = NULL;

    solver->marked = allocate_and_clear_block (solver->variables);
    INIT(solver->clause);
    solver->trivial = false;

    return solver;
}

void gimsatul_add (gimsatul *solver, int signed_lit) {
    // Adapted from parse.c/parse_dimacs_body()
    if (signed_lit) {
        unsigned idx = abs (signed_lit) - 1;
        assert (idx < (unsigned) solver->variables);
        signed char sign = (signed_lit < 0) ? -1 : 1;
        signed char mark = solver->marked[idx];
        unsigned unsigned_lit = 2 * idx + (sign < 0);
#ifndef NDEBUG
        PUSH (*original, unsigned_lit);
#endif
        if (mark == -sign) {
            ROG ("skipping trivial clause");
            solver->trivial = true;
        } else if (!mark) {
            PUSH (solver->clause, unsigned_lit);
            solver->marked[idx] = sign;
        } else
            assert (mark == sign);
    } else {        // if clause finished
#ifndef NDEBUG
        PUSH (*original, INVALID);
#endif
        unsigned *literals = solver->clause.begin;
        if (!solver->ruler->inconsistent && !solver->trivial) {
            const size_t size = SIZE (solver->clause);
            assert (size <= solver->ruler->size);
            if (!size) {
                assert (!solver->ruler->inconsistent);
                very_verbose (0, "%s", "found empty original clause");
                solver->ruler->inconsistent = true;
            } else if (size == 1) {
                const unsigned unit = *(solver->clause.begin);
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
                ROGCLAUSE (large_clause, "new");
                PUSH (solver->ruler->clauses, large_clause);
            }
        } else
            solver->trivial = false;
        for (all_elements_on_stack (unsigned, unsigned_lit, solver->clause))
            solver->marked[IDX (unsigned_lit)] = 0;
        CLEAR (solver->clause);
    }
}

int gimsatul_solve (gimsatul *solver) {
    // Adapted from gimsatul.c/main()
    simplify_ruler(solver->ruler);
    clone_rings(solver->ruler);
    struct ring *winner = slove_rings(solver->ruler);
    signed char *witness = extend_witness(winner);
    // check_witness(witness, solver->ruler->original);
    solver->witness = witness;
    return winner ? winner->status : 0;
}

int gimsatul_value (gimsatul *solver, int lit) {
    return lit * solver->witness[lit];
}

void gimsatul_release (gimsatul *solver) {
    detach_and_delete_rings(solver->ruler);
    delete_ruler(solver->ruler);
    free(solver->marked);
    free(solver);
}
