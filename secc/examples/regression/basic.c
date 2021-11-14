void nullptr()
{
	void *p = NULL;
	if(p) {
		_(assert false)
	}
}

void incons()
	_(requires false)
{
}

void disjoint(int * x)
  _(requires exists int v. x |-> v)
  _(requires exists int v2. x |-> v2)
  _(ensures (1 == 0))
  _(lemma)
{
}

void disjoint2()
  _(requires exists int *p, int _p. p |-> _p)
  _(requires exists int *q, int _q. q |-> _q)
  _(requires p == q)
  _(ensures (1 == 0))
  _(lemma)
{
}

int old_post(int x)
	_(ensures result == x + 1)
{
	x = x + 1;
	return x;
}

void old_mod(int x)
	_(requires x == 0)
	_(ensures  x == 0)
{
	x ++;
}

void scope() {
	int x = 0;
	{
		int x = 1;
		_(assert x == 1)
	}
	_(assert x == 0)
}

/* Issue 17: now fixed */
int test(int x)
  _(requires x :: low)
  _(fails incorrect)
{
  if (x <= 0){
    return 0;
  }
  _(assert (1 == 0))
}