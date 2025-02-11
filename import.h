#ifndef _import_h_INCLUDED
#define _import_h_INCLUDED

#include "clause.h"

#include <stdbool.h>

struct ring;
struct watch;
bool import_shared (struct ring *);
void gimsatul_import_redundant_clauses (struct ring *);
bool import_large_clause_from_mallob (struct ring *, struct clause *);
bool import_binary_from_mallob (struct ring *, struct watch *);

#endif
