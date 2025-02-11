#include "export.h"
#include "message.h"
#include "random.h"
#include "ruler.h"
#include "utilities.h"
#include "libgimsatul.h"

#define LD_MAX_VAR 30u

#define EXTERNAL_MAX_VAR ((1 << LD_MAX_VAR) - 1)

#define VALID_EXTERNAL_LITERAL(LIT) \
  ((LIT) && ((LIT) != INT_MIN) && ABS (LIT) <= EXTERNAL_MAX_VAR)

#define NEGATED(LIT) ((LIT) &1u)

static bool exporting (struct ring *ring) {
  unsigned threads = ring->threads;
  if (threads < 2)
    return false;
  if (!ring->options.share_learned)
    return false;
  return true;
}

static struct rings *export_rings (struct ring *ring) {

  struct ruler *ruler = ring->ruler;
  struct rings *rings = &ruler->rings;
  unsigned size = SIZE (*rings);

  struct rings *exports = &ring->exports;
  CLEAR (*exports);

  unsigned export = ring->options.export;
  if (export == 1) {
    struct ring *other = random_other_ring (ring);
    assert (other != ring);
    LOG ("export to single ring %u", other->id);
    PUSH (*exports, other);
  } else if (export == 2) {
    unsigned target = log2ceil (size);
    unsigned start = ring->id;
    do {
      unsigned id = random_modulo (&ring->random, size);
      if (id == start)
        continue;
      struct ring *other = PEEK (*rings, id);
      for (all_pointers_on_stack (struct ring, tmp, *exports))
        if (tmp == other)
          goto CONTINUE;
      LOG ("logarithmic export to ring %u", id);
      PUSH (*exports, other);
    CONTINUE:;
    } while (SIZE (*exports) != target);
  } else {
    LOG ("export to all %u other rings", size - 1);
    for (all_pointers_on_stack (struct ring, other, *rings))
      if (other != ring)
        PUSH (*exports, other);
  }

  return exports;
}

static void export_to_ring (struct ring *ring, struct ring *other,
                            struct clause *clause, unsigned glue,
                            unsigned size, uint64_t redundancy) {
  LOG ("trying to export to target ring %u with redundancy [%u:%u]",
       other->id, LOG_REDUNDANCY (redundancy));
  assert (ring != other);

  struct pool *pool = ring->pool + other->id;

  struct bucket *start = pool->bucket;
  struct bucket *end = start + SIZE_POOL;
  struct bucket *worst = 0;

  uint64_t worst_redundancy = 0;

  for (struct bucket *b = start; b != end; b++) {
    uint64_t b_redundancy = b->redundancy;
    if (!b->shared) {
      worst_redundancy = b_redundancy;
      worst = b;
      break;
    }
    if (worst_redundancy > b_redundancy)
      continue;
    worst_redundancy = b_redundancy;
    worst = b;
  }

  if (!worst) {
    LOG ("export to ring %u failed "
         "as all its buckets have better redundancy",
         other->id);
    return;
  }

#ifdef LOGGING
  if (worst_redundancy == MAX_REDUNDANCY)
    LOG ("exporting to ring %u bucket %zu (first export)", other->id,
         worst - start);
  else
    LOG ("exporting to ring %u bucket %zu with redundancy [%u:%u]",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
#endif
  if (!is_binary_pointer (clause))
    reference_clause (ring, clause, 1);

  atomic_uintptr_t *share = &worst->shared;
  uintptr_t ptr = atomic_exchange (share, (uintptr_t) clause);
  worst->redundancy = redundancy;

  if (ptr) {
    assert (worst_redundancy != MAX_REDUNDANCY);
    LOG ("previous export to ring %u bucket %zu redundancy [%u:%u] failed",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
    struct clause *previous = (struct clause *) ptr;
    if (!is_binary_pointer (previous))
      dereference_clause (ring, previous);
  } else if (worst_redundancy != MAX_REDUNDANCY) {
    LOG ("previous export to ring %u bucket %zu redundancy [%u:%u] "
         "succeeded",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
    INC_LARGE_CLAUSE_STATISTICS (exported, glue, size);
  }
}


// export functionality for Mallob
// --------------------------------------

void gimsatul_export_redundant_clause (struct ring *ring, unsigned glue, unsigned size, unsigned *lits) {
  //printf(">> gimsatul_export_redundant_clause\n");
  if (!ring->consume_clause) return;
  if (size > ring->consume_clause_max_size) return;
  glue = MAX(glue, 1);
  glue = MIN(glue, size-1);
  // Export clause.
  for (unsigned i = 0; i < size; i++) {
    // Externalize each literal
    const unsigned ilit = lits[i];
    const int elit = unmap_and_export_literal(ring->ruler->unmap, ilit);
    ring->consume_clause_buffer[ring->id][i] = elit;
  }
  // Execute learnt clause callback
  ring->consume_clause (ring->consume_clause_state, size, glue, ring->id); // add pointer to lits
}
// --------------------------------------

void export_units (struct ring *ring, bool export_to_mallob) {
  struct ruler *ruler = ring->ruler;
  struct ring_units *units = &ring->ring_units;
  volatile signed char *values = ruler->values;
  unsigned *end = units->end;
  bool locked = false;
  while (units->export != end) {
    assert (units->export < units->end);
    unsigned unit = *units->export ++;
#ifndef NFASTPATH
    if (values[unit])
      continue;
#endif
    if (ring->pool && !locked) {
      if (pthread_mutex_lock (&ruler->locks.units))
        fatal_error ("failed to acquire unit lock");
      locked = true;
    }

    signed char value = values[unit];
    if (value)
      continue;

    very_verbose (ring, "exporting unit %d",
                  unmap_and_export_literal (ruler->unmap, unit));
    assign_ruler_unit (ruler, unit);
    
    if (export_to_mallob) {
      unsigned *lits = &unit;
      gimsatul_export_redundant_clause (ring, 1, 1, lits);
    }

    INC_UNIT_CLAUSE_STATISTICS (exported);
  }

  if (locked && pthread_mutex_unlock (&ruler->locks.units))
    fatal_error ("failed to release unit lock");
}

static void export_clause (struct ring *ring, struct clause *clause, bool export_to_mallob) {
  assert (exporting (ring));
  bool binary = is_binary_pointer (clause);
  unsigned glue = binary ? 1 : clause->glue;
  unsigned size = binary ? 2 : clause->size;
  bool share_by_size = ring->options.share_by_size;
  uint64_t high = share_by_size ? size : glue;
  uint64_t low = share_by_size ? glue : size;
  uint64_t redundancy = (high << 32) + low;
  struct rings *exports = export_rings (ring);
  for (all_pointers_on_stack (struct ring, other, *exports)) {
    export_to_ring (ring, other, clause, glue, size, redundancy);
  }
  
  // export to Mallob
  if (!export_to_mallob)
    return;
  if (!binary)
    gimsatul_export_redundant_clause (ring, glue, size, clause->literals);
  else {
    unsigned lits[] = {lit_pointer(clause), other_pointer(clause)};
    gimsatul_export_redundant_clause (ring, glue, size, lits);
  }
}

void export_binary_clause (struct ring *ring, struct watch *watch, bool export_to_mallob) {
  assert (is_binary_pointer (watch));
  if (!exporting (ring))
    return;
  LOGWATCH (watch, "exporting");
  struct clause *clause = (struct clause *) watch;
  export_clause (ring, clause, export_to_mallob);
}

void export_large_clause (struct ring *ring, struct clause *clause) {
  assert (!is_binary_pointer (clause));
  if (!exporting (ring))
    return;
  struct averages *a = ring->averages + ring->stable;
  unsigned glue = clause->glue;
  if (glue > ring->tier1_glue_limit[ring->stable]) {
    double factor = 0.5;
    double average = a->glue.slow.value;
    double limit = factor * average;
    if (glue > limit) {
      LOGCLAUSE (clause, "failed to export (glue %u > limit %g = %g * %g)",
                 glue, limit, factor, average);
      return;
    }
    unsigned size = clause->size;
    factor = 1.0;
    average = a->size.value;
    limit = factor * average;
    if (size > limit) {
      LOGCLAUSE (clause, "failed to export (size %u > limit %g = %g * %g)",
                 size, limit, factor, average);
      return;
    }
  }
  LOGCLAUSE (clause, "exporting");
  export_clause (ring, clause, true);
}

void flush_pool (struct ring *ring) {
#ifndef QUIET
  size_t flushed = 0;
#endif
  for (unsigned i = 0; i != ring->threads; i++) {
    if (i == ring->id)
      continue;
    struct pool *pool = ring->pool + i;
    for (unsigned shared = 0; shared != SIZE_POOL; shared++) {
      struct bucket *b = &pool->bucket[shared];
      atomic_uintptr_t *share = &b->shared;
      uintptr_t ptr = atomic_exchange (share, 0);
      if (!ptr)
        continue;
      struct clause *clause = (struct clause *) ptr;
      if (!is_binary_pointer (clause))
        dereference_clause (ring, clause);
#ifndef QUIET
      flushed++;
#endif
    }
  }
  very_verbose (ring, "flushed %zu clauses to be exported", flushed);
}
