#ifndef _reduce_h_INCLUDED
#define _reduce_h_INCLUDED

#include <stdbool.h>

struct ring;
bool reducing (struct ring *);
void reduce (struct ring *);

#endif
