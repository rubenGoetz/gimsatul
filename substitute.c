#include "message.h"
#include "ruler.h"
#include "simplify.h"
#include "substitute.h"
#include "trace.h"
#include "utilities.h"

static unsigned *
find_equivalent_literals (struct ruler * ruler, unsigned round)
{
  size_t bytes = 2*ruler->size * sizeof (unsigned);
  unsigned * marks = allocate_and_clear_block (bytes);
  unsigned * reaches = allocate_and_clear_block (bytes);
  unsigned * repr = allocate_block (bytes);
  for (all_ruler_literals (lit))
    repr[lit] = lit;
  struct unsigneds scc;
  struct unsigneds work;
  INIT (scc);
  INIT (work);
  bool * eliminated = ruler->eliminated;
  signed char * values = (signed char*) ruler->values;
  unsigned marked = 0, equivalences = 0;
  for (all_ruler_literals (root))
    {
      if (eliminated[IDX (root)])
	continue;
      if (values[root])
	continue;
      if (marks[root])
	continue;
      assert (EMPTY (scc));
      assert (EMPTY (work));
      assert (marked < UINT_MAX);
      PUSH (work, root);
      while (!EMPTY (work))
	{
	  unsigned lit = POP (work);
	  if (lit == INVALID)
	    {
	      lit = POP (work);
	      unsigned not_lit = NOT (lit);
	      unsigned lit_reaches = reaches[lit];
              struct clauses * clauses = &OCCURRENCES (not_lit);
	      for (all_clauses (clause, *clauses))
		{
		  if (!binary_pointer (clause))
		    continue;
		  unsigned other = other_pointer (clause);
		  if (values[other])
		    continue;
		  if (eliminated[IDX (other)])
		    continue;
		  unsigned other_reaches = reaches[other];
		  if (other_reaches < lit_reaches)
		    lit_reaches = other_reaches;
		}
	      reaches[lit] = lit_reaches;
	      unsigned lit_mark = marks[lit];
	      if (lit_reaches != lit_mark)
		continue;
	      unsigned * end = scc.end, * p = end, other, new_repr = lit;
	      while ((other = *--p) != lit)
		if (other < new_repr)
		  new_repr = other;
	      scc.end = p;
	      while (p != end)
		{
		  unsigned other = *p++;
		  reaches[other] = INVALID;
		  if (other == new_repr)
		    continue;
		  repr[other] = new_repr;
		  equivalences++;
		  ROG ("literal %s is equivalent to representative %s",
		       ROGLIT (other), ROGLIT (new_repr));
		  if (other == NOT (new_repr))
		    {
		      very_verbose (0, "%s", "empty resolvent");
		      trace_add_unit (&ruler->buffer, other);
		      assign_ruler_unit (ruler, other);
		      trace_add_empty (&ruler->buffer);
		      ruler->inconsistent = true;
		      goto DONE;
		    }
		}
	    }
	  else
	    {
	      if (marks[lit])
		continue;
	      assert (marked < UINT_MAX);
	      reaches[lit] = marks[lit] = ++marked;
	      PUSH (work, lit);
	      PUSH (work, INVALID);
	      PUSH (scc, lit);
	      unsigned not_lit = NOT (lit);
              struct clauses * clauses = &OCCURRENCES (not_lit);
	      for (all_clauses (clause, *clauses))
		{
		  if (!binary_pointer (clause))
		    continue;
		  unsigned other = other_pointer (clause);
		  if (values[other])
		    continue;
		  if (eliminated[IDX (other)])
		    continue;
		  if (marks[other])
		    continue;
		  PUSH (work, other);
		}
	    }
	}
    }
DONE:
  RELEASE (scc);
  RELEASE (work);
  free (reaches);
  free (marks);
  verbose (0, "[%u] found %u new equivalent literal pairs",
	  round, equivalences);
  if (equivalences && !ruler->inconsistent)
    return repr;
  free (repr);
  return 0;
}

static void
substitute_clause (struct ruler * ruler,
                   unsigned src, unsigned dst, struct clause * clause)
{
  ROGCLAUSE (clause, "substituting");
  signed char * values = (signed char*) ruler->values;
  signed char dst_value = values[dst];
  if (dst_value > 0)
    {
      ROG ("satisfied replacement literal %s", ROGLIT (dst));
      return;
    }
  struct unsigneds * resolvent = &ruler->resolvent;
  CLEAR (*resolvent);
  unsigned not_dst = NOT (dst);
  if (binary_pointer (clause))
    {
      assert (lit_pointer (clause) == src);
      unsigned other = other_pointer (clause);
      if (other == not_dst)
	{
	  ROG ("resulting clause tautological since it "
	       "contains both %s and %s",
	       ROGLIT (dst), ROGLIT (other));
	  return;
	}
      if (other != dst)
	{
	  signed char other_value = values[other];
	  if (other_value > 0)
	    {
	      ROG ("clause already satisfied by %s", ROGLIT (other));
	      return;
	    }
	  if (!other_value)
	    PUSH (*resolvent, other);
	}
    }
  else
    {
      for (all_literals_in_clause (other, clause))
	{
	  if (other == src)
	    continue;
	  if (other == dst)
	    continue;
	  if (other == not_dst)
	    {
	      ROG ("resulting clause tautological since it "
		   "contains both %s and %s",
		   ROGLIT (dst), ROGLIT (other));
	      return;
	    }
	  signed char other_value = values[other];
	  if (other_value < 0)
	    continue;
	  if (other_value > 0)
	    {
	      ROG ("clause already satisfied by %s", ROGLIT (other));
	      return;
	    }
	  PUSH (*resolvent, other);
	}
    }
  if (!dst_value)
    PUSH (*resolvent, dst);
  add_resolvent (ruler);
}

static unsigned
substitute_literal (struct ruler * ruler, unsigned src, unsigned dst)
{
  if (ruler->values[src])
    return 0;
  ROG ("substituting literal %s with %s", ROGLIT (src), ROGLIT (dst));
  assert (!ruler->eliminated[IDX (src)]);
  assert (!ruler->eliminated[IDX (dst)]);
  assert (src != NOT (dst));
  assert (dst < src);
  struct clauses * clauses = &OCCURRENCES (src);
  for (all_clauses (clause, *clauses))
    {
      substitute_clause (ruler, src, dst, clause);
      if (ruler->inconsistent)
	break;
      disconnect_and_delete_clause (ruler, clause, src);
    }
  RELEASE (*clauses);
  struct unsigneds * extension = &ruler->extension;
  ROGBINARY (NOT (src), dst,
             "pushing on extension stack with witness literal %s",
	     ROGLIT (NOT (src)));
  PUSH (*extension, INVALID);
  PUSH (*extension, src);
  PUSH (*extension, NOT (dst));
  if (SGN (src))
    {
      unsigned idx = IDX (src);
      ROG ("marking %s as aliminated", ROGVAR (idx));
      ruler->statistics.substituted++;
      assert (ruler->statistics.active);
      ruler->statistics.active--;
      assert (!ruler->eliminated[idx]);
      ruler->eliminated[idx] = 1;
    }
  return 1;
}

static unsigned
substitute_equivalent_literals (struct ruler * ruler, unsigned * repr)
{
  unsigned other;

  if (proof.file)
    for (all_positive_ruler_literals (lit))
      if ((other = repr[lit]) != lit)
	{
	  trace_add_binary (&ruler->buffer, NOT (lit), other);
	  trace_add_binary (&ruler->buffer, lit, NOT (other));
	}

  unsigned substituted = 0;
  for (all_ruler_literals (lit))
    if ((other = repr[lit]) != lit)
      {
	substituted += substitute_literal (ruler, lit, other);
	if (ruler->inconsistent)
	  break;
      }

  if (proof.file)
    for (all_positive_ruler_literals (lit))
      if ((other = repr[lit]) != lit)
	{
	  trace_delete_binary (&ruler->buffer, NOT (lit), other);
	  trace_delete_binary (&ruler->buffer, lit, NOT (other));
	}

  RELEASE (ruler->resolvent);

  return substituted;
}

bool
equivalent_literal_substitution (struct ruler * ruler, unsigned round)
{
  double substitution_start = START (ruler, substituting);
  unsigned * repr = find_equivalent_literals (ruler, round);
  unsigned substituted = 0;
  if (repr)
    {
      substituted = substitute_equivalent_literals (ruler, repr);
      free (repr);
    }
  double substitution_end = STOP (ruler, substituting);
  if (verbosity >= 0)
    fputs ("c\n", stdout);
  message (0, "[%u] substituted %u variables %.0f%% in %.2f seconds",
           round, substituted, percent (substituted, ruler->size),
	   substitution_end - substitution_start);
  return substituted;
}
