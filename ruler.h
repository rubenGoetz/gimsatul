#ifndef _ruler_h_INCLUDED
#define _ruler_h_INCLUDED

#include "barrier.h"
#include "clause.h"
#include "options.h"
#include "profile.h"
#include "ring.h"
#include "stack.h"

#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>

struct ruler_trail {
  unsigned *begin;
  unsigned *propagate;
  unsigned *volatile end;
};

#define LOCKS \
  LOCK (rings) \
  LOCK (simplify) \
  LOCK (terminate) \
  LOCK (units) \
  LOCK (winner)

struct ruler_locks {
#define LOCK(NAME) pthread_mutex_t NAME;
  LOCKS
#undef LOCK
};

#define BARRIERS \
  BARRIER (copy) \
  BARRIER (end) \
  BARRIER (import) \
  BARRIER (run) \
  BARRIER (start) \
  BARRIER (unclone)

struct ruler_barriers {
#define BARRIER(NAME) struct barrier NAME;
  BARRIERS
#undef BARRIER
};

struct ruler_last {
  unsigned fixed;
  uint64_t garbage;
  uint64_t search;
};

struct ruler_limits {
  bool initialized;

  uint64_t elimination;
  uint64_t subsumption;

  size_t clause_size_limit;
  size_t occurrence_limit;

  unsigned current_bound;
  unsigned max_bound;
  unsigned max_rounds;
};

struct ruler {
  unsigned size;
  unsigned compact;

  struct ring *volatile winner;

  volatile bool terminate;
  volatile bool simplify;

  bool eliminating;
  bool inconsistent;
  bool simplifying;
  bool solving;
  bool subsuming;

  bool *eliminate;
  bool *subsume;

  struct clauses *occurrences;
  pthread_t *threads;
  unsigned *unmap;    // internal => original
  unsigned *map;      // original => internal
  bool map_filled;    // TODO: check if necessary
  signed char volatile *values;

  struct ruler_barriers barriers;
  struct ruler_locks locks;

  struct clauses clauses;
  struct unsigneds extension[2];
#ifndef NDEBUG
  struct unsigneds *original;
#endif
  struct rings rings;
  struct ruler_trail units;

  struct trace trace;

  struct ruler_last last;
  struct ruler_limits limits;
  struct options options;
  struct ruler_profiles profiles;
  struct ruler_statistics statistics;

  // Clause export
  void *consume_clause_state;
  int **consume_clause_buffer;
  unsigned consume_clause_max_size;
  void (*consume_clause) (void *state, int size, int glue, int ring_id);
  
  // Clause import
  void *produce_clause_state;
  void (*produce_clause) (void *state, int **clause, int *size, int *glue);
  unsigned long num_conflicts_at_last_import;
  struct unsigneds *mallob_import_clause;

  // Additional statistics
  unsigned long num_imported_external_clauses;
  unsigned long num_discarded_external_clauses;
  unsigned long r_ee,r_ed,r_pb,r_ss,r_sw,r_tr,r_fx,r_ia,r_tl;
  // r_fx == fixed=true
  // r_ed == eliminated variable

  // Initial phase
  bool initial_phase_defined;
  char **initial_phases_pointer;
};

/*------------------------------------------------------------------------*/

#define OCCURRENCES(LIT) (ruler->occurrences[LIT])

/*------------------------------------------------------------------------*/

#define all_rings(RING) \
  all_pointers_on_stack (struct ring, RING, ruler->rings)

#define all_ruler_indices(IDX) \
  unsigned IDX = 0, END_##IDX = ruler->compact; \
  IDX != END_##IDX; \
  ++IDX

#define all_ruler_literals(LIT) \
  unsigned LIT = 0, END_##LIT = 2 * ruler->compact; \
  LIT != END_##LIT; \
  ++LIT

#define all_positive_ruler_literals(LIT) \
  unsigned LIT = 0, END_##LIT = 2 * ruler->compact; \
  LIT != END_##LIT; \
  LIT += 2

/*------------------------------------------------------------------------*/

struct ruler *new_ruler (size_t size, struct options *);
void delete_ruler (struct ruler *);

void flush_large_clause_occurrences (struct ruler *);

void new_ruler_binary_clause (struct ruler *, unsigned, unsigned);
void assign_ruler_unit (struct ruler *, unsigned unit);

void connect_large_clause (struct ruler *, struct clause *);

void disconnect_literal (struct ruler *, unsigned, struct clause *);

void push_ring (struct ruler *, struct ring *);
void detach_ring (struct ring *);
void set_winner (struct ring *);

void set_terminate (struct ruler *, struct ring *);

void print_ruler_profiles (struct ruler *);

/*------------------------------------------------------------------------*/

static inline void connect_literal (struct ruler *ruler, unsigned lit,
                                    struct clause *clause) {
  PUSH (OCCURRENCES (lit), clause);
}

struct ring *first_ring (struct ruler *);

#endif
