#ifndef _export_h_INCLUDED
#define _export_h_INCLUDED

#include <stdbool.h>

struct clause;
struct ring;
struct watch;

void export_units (struct ring *, bool);
void export_binary_clause (struct ring *, struct watch *, bool);
void export_large_clause (struct ring *, struct clause *);
void flush_pool (struct ring *);

#endif
