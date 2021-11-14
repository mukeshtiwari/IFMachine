int *alloc();
	_(ensures exists int v. result |-> v)

void free(int *x);
	_(requires exists int v. x |-> v)

void branch(int p)
	_(fails insecure) // we don't know for sure, though
{
	if(p) {}
}

int zero()
	_(ensures result == 0)
	_(ensures result :: low)
{
	return 0;
}

void secure1(int *p)
	_(requires exists int v.
		p |-> v)
	_(ensures exists int v.
		p |-> v && v :: low)
{
	*p = 0;
}

void secure2(int *out, int in)
	_(requires in :: low)
	_(requires exists int v.
		out |->[low] v)
	_(ensures
		out |->[low] in)
{
	*out = in;
}

int secure3()
	_(ensures result :: low)
{
	int *x = alloc();
	secure1(x);
	int y = *x;
	free(x);
	return y;
}

void secure4(int y)
	_(requires y :: low)
{
	if(y) {}
}

void insecure1(int *p)
	_(fails insecure)
	_(requires exists int v.
		p |-> v)
	_(ensures
		p |-> v && v :: low)
{
	*p = *p;
}

void insecure2(int *out, int in)
	_(fails insecure)
	_(requires in :: high)
	_(requires exists int v.
		out |->[low] v)
	_(ensures
		out |->[low] in)
{
	*out = in;
}


int insecure3(int z)
	_(fails insecure)
	_(ensures result :: low)
{
	int *x = alloc();
	secure1(x);
	int y = *x + z;
	return y;
}

void insecure4(int y)
	_(fails insecure)
{
	if(y) {}
}

/* Doesn't work in Prabawa et al, VMCAI 2018
   Can be proved easily by SecC */
int fig4(int p)
{
  int b = (p == p);
  if(b) return 10; else return 9;
}

void conditional(int b, int *p)
	_(requires b :: low)
	_(requires b != 0 ==> exists int v. p |-> v)
	_(ensures  b != 0 ==> p |-> 0)
{
	if(b) *p = 0;
}

void assign(int *p, int x)
	_(requires exists sec s, int v. p |->[s] v)
	_(requires x :: s)
	_(ensures p |->[s] x)
{
	*p = x;
}

void assign_insecure(int *p, int x)
	_(fails insecure)
	_(requires exists sec s, int v. p |->[s] v)
	_(requires x :: high)
	_(ensures p |->[s] x)
{
	*p = x;
}

void lowmem_insecure(int *p)
  _(fails incorrect) // TODO: should probably be insecure
  _(requires exists int v. p |-> v && p :: low && v :: low)
  _(ensures p |->[low] v)
{
  *p = 0;
}

void test_bind1_checked(int * x, int n);
  _(requires n == 0 ==> x |-> n)


/* this should fail because, at present, proving the precondition
   requires splitting on (n == 0) which is not known to be low */
void test_bind1_checked_insecure(int *x, int n)
  _(requires x |-> n)
  _(fails insecure)
{
  test_bind1_checked(x,n);
}

/* note that the x |-> n gets consumed only when n == 0. Hence,
   we still need to mention it in the postcondition otherwise. */
void test_bind1_checked_secure(int *x, int n)
  _(requires x |-> n)
  _(requires (n == 0) :: low)
  _(ensures n != 0 ==> x |-> n)
{
  test_bind1_checked(x,n);
}

/* this program is designed to illustrate the unsoundness that can
 * arise if we do not carefully check that assertions that will be
 * case split upon are low. In particular, if we make a case
 * distinction on x > 0, then in either case (x > 0)::low is
 * provable. Once we have (unsoundly) established that fact, we can
 * then of course falsely claim to return low data */
int check_split_insecure_consume(int x)
  _(ensures result :: low)
  _(fails insecure) // XXX: for technical reasons, this is not flagged as insecure but incorrect
{
  _(assert(x > 0 ? (x > 0)::low : (x > 0)::low))
  return (x > 0);
}


/* this might seem a bit harsh to disallow. Unlike the example
 * above we are now using an assume statement. In some sense, if
 * you use an assume statement you are being dangerous. However,
 * we would like to limit the degree of danger. Specifically,
 * we want to avoid the case where we assume something and
 * then, subsequently, do unsound reasoning (regardless of whether
 * that assumption was valid or not). Reasoning from conditional
 * assertions is by case analysis and, as we saw above, that is
 * sound only when the condition is low. Hence, why this is
 * rightly judged insecure. */
int check_split_insecure_produce(int x)
  _(ensures result :: low)
  _(fails insecure) // XXX: the above currently applies only for spatial assertions, pure and relational ones are not split explicitly
{
  _(assume(x > 0 ? (x > 0)::low : (x > 0)::low))
  return (x > 0);
}

void sec_high(int x)
{
  _(assert x :: high)
}

void high_ptr_write(int x, int *p)
  _(maintains exists int _p. p |-> _p)
{
  *p = x;
}

/* we can prove x :: lev for any lev strictly above the attacker level.
   Note the lev :: attacker ensures that the value 'lev' denoting the
   level it not itself sensitive */
void sec_meaning(int x)
  _(requires exists sec lev. lev :: attacker && attacker <= lev && attacker != lev)
{
  _(assert x :: lev)
}

/* we can branch on all values visible to the attacker: of course a value v
   that is visible to an arbitrary attacker must be visible to all
   potential attackers, in which case v :: low will follow */
int secure_branch(int b)
  _(requires b :: attacker)
  _(ensures result :: low)
{
  if(b){
    return 0;
  }else{
    return 1;
  }
}

/* issue 27: we need to be careful about the relational encoding of <=> */
int eqv_sec()
  _(requires exists bool b, bool c. b == c)
  _(requires b :: low)
{
  _(assert c :: low)
}

void eqv_sec2(int x)
{
  int y = x;
  _(assert (x :: low) <=> (y :: low))

}

/* note that for boolean connectives, including ==,
   if any of their arguments are relational, then the connective
   is interpreted relationally. Hence the following
   program rightly doesn't verify since the precondition is encoded
   as: (b /\ b') == (x == x')
   This is not sufficient to derive b == b'
*/
void relational_eqv(int x)
  _(requires exists bool b. b == (x :: low))
  _(fails insecure)
{
  _(assert b :: low)
}