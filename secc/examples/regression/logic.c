_(constant
	int zero = 0)

_(constant
	int nonzero)

_(axioms
	zero != nonzero)

_(function
	int max(int n, int m))

_(function
	int inc(int i) = i + 1)

_(rewrites
	forall int n, int m. n < m ==> max(n, m) == m)

int fundef(int n)
	_(ensures result == inc(n))
{
	return n + 1;
}

int rw(int n, int m)
	_(requires n < m)
	_(ensures result == max(n, m))
{
	return m;
}

void ax_rw()
	_(ensures nonzero != zero)
{
}

/* Issue #21 and quantification over security labels */

_(function sec join(sec a, sec b))

_(axioms
  forall sec a, sec b. a <= join(a,b) && b <= join(a,b) && join(a,a) == a)

void join(int x, int y)
_(ensures forall sec lx, sec ly. x :: lx && y :: ly ==> result :: join(lx,ly))
{
  return (x + y);
}

int meh(int x, int y)
  _(requires x :: low)
  _(requires y :: low)
  _(ensures result :: low)
{
  return join(x,y);
}


int join2(int x, int y)
  _(requires exists sec lx. x :: lx)
  _(requires exists sec ly. y :: ly)
  _(ensures result :: join(lx,ly))
{
  return (x + y);
}

/* note that join2's spec is too weak to allow SecC to conclude result :: low */
int meh2(int x, int y)
  _(requires x :: low)
  _(requires y :: low)
{
  return join2(x,y);
}


_(function sec int2sec(int x))

_(axioms
  int2sec(0) == low)

/* existentially quantifying over the levels of x and y in the precondition
 * gives a specification that is too weak for SecCSL. Even if we know x :: low,
 * SecC won't conclude that in `exists sec lx. x :: lx` lx must be low.
 * Instead we use ghost variables to allow the caller to specify the levels.
 */
void join3(int x, int y, int ghost_lx, int ghost_ly)
_(requires x :: int2sec(ghost_lx))
_(requires y :: int2sec(ghost_ly))
_(ensures result :: join(int2sec(ghost_lx),int2sec(ghost_ly)))
{
  return (x + y);
}


int meh3(int x, int y)
  _(requires x :: low)
  _(requires y :: low)
  _(ensures result :: low)
{
  return join3(x,y,0,0);
}

void logic_map(int k)
	_(requires exists map<int,int> a.
		forall int i. a[i] == 0)
	_(ensures a[k] == 0)
{
}

/* XXX: timeout
void logic_map2(int k)
	_(requires exists map<int,int> a.
		forall int i. a[i] == 0)
	_(ensures a[k] == 1)
	_(fails incorrect)
{
}
*/

void logic_map_update(int k)
	_(requires exists map<int,int> a.
		forall int i. a[i] == 0)
	_(ensures a[k:=1][k] == 1)
{
}

// polymorphic lists
_(function
	bool contains(list<$a> xs, $a x))

_(rewrites
	forall $a x. contains(nil, x) <=> false;
	forall $a x, $a y, list<$a> ys. contains(cons(y,ys), x) <=> (x == y) || contains(ys, x))

void polymorphic_contains(int x)
	_(requires exists list<int> xs. true)
{
	_(xs = cons(x, xs);)
	_(assert contains(xs, x))
}

/* test that _apply properly preserves the pure mode */
void non_negative_numbers_are_not_negative(int x)
  _(pure) _(lemma)
  _(requires x >= 0)
  _(ensures !(x < 0))
{
  _(apply
  if (x == 0) {
  } else {
  }
 )
}