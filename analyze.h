#ifndef _analyze_h_INCLUDED
#define _analyze_h_INCLUDED

#include <stdbool.h>

struct ring;
struct watch;

bool analyze (struct ring *, struct watch *conflict);
void clear_analyzed (struct ring *);
void eagerly_subsume_last_learned (struct ring *);
void sort_deduced_clause (struct ring *);
void insert_last_learned (struct ring *ring, struct watch *learned);

#endif
