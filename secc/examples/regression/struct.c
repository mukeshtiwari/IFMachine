#include "secc.h"

struct pair {
  int a;
  int b;
};


_(function struct pair _make_pair(int a, int b))

_(axioms
  forall int a, int b. _make_pair(a,b).a == a;
  forall int a, int b. _make_pair(a,b).b == b;
  forall struct pair p. _make_pair(p.a,p.b) == p)

void zero_pair(struct pair *p)
_(requires exists int _a, int _b. &p->a |-> _a && &p->b |-> _b)
_(ensures exists int _ra, int _rb. &p->a |-> _ra && &p->b |-> _rb)
_(ensures _make_pair(_ra,_rb) == _make_pair(0,0))
{
  p->a = 0;
  p->b = 0;
}
