#include "secc.h"

/* Constant-time Test for Memory Equality */

#if __SECC
/* needed to work around limitations of SecC's type system */
_(function int abs_toint(bool b))

_(axioms
  abs_toint(true) == 1;
  abs_toint(false) == 0)


/* needed to work around bug in SecC -- see below the specification of
   memcmp where this is used */
_(function bool list_eq(list<int> l1, list<int> l2))

_(rewrites
  forall list<int> l1, list<int> l2. list_eq(l1,l2) <=> (l1 == l2))


_(predicate ar(int *p; int n, list<int> s)
  (0 < n ==> exists int x, list<int> tl. s == cons(x,tl) &&
             p |-> x && ar(p+1; n-1, tl)) &&
  (n == 0 ==> s == nil))


void ar_zero_nil(int *p, list<int> xs)
  _(requires ar(p; 0, xs))
  _(ensures xs == nil)
  _(ensures ar(p; 0, xs))
  _(lemma)
{
  _(unfold ar(p; 0, xs))
  _(fold ar(p; 0, xs))
}

void ar_nonzero_cons(int *p, int n, list<int> xs)
  _(requires ar(p; n, xs))
  _(requires n > 0)
  _(ensures exists int hd, list<int> tl. xs == cons(hd,tl))
  _(ensures ar(p; n, xs))
  _(lemma)
{
  _(unfold ar(p; n, xs))
  _(fold ar(p; n, xs))
}


/* not used but is illustrative */
void and_lemma(int a1, int a2, int a3, bool b1, bool b2)
  _(requires a1 <=> b1)
  _(requires a2 <=> b2)
  _(requires a1 >= 0)
  _(requires a2 >= 0)  
  _(requires a3 <= a1 && a3 <= a2 && (a3 == a1 || a3 == a2))
  _(ensures a3 <=> (b1 && b2))
  _(lemma)
{
}

/* not used but is illustrative */
void or_lemma(int a1, int a2, int a3, bool b1, bool b2)
  _(requires a1 <=> b1)
  _(requires a2 <=> b2)
  _(requires a1 >= 0)
  _(requires a2 >= 0)  
  _(requires a3 >= a1 && a3 >= a2 && (a3 == a1 || a3 == a2))
  _(ensures a3 <=> (b1 || b2))
  _(lemma)
{
}

#endif // __SECC

#if __SECC
_(function int abs_choose(int c, int a, int b))

_(rewrites
  forall int c, int a, int b. c == 0 ==> abs_choose(c, a, b) == b;
  forall int c, int a, int b. c == 1 ==> abs_choose(c, a, b) == a)


void abs_choose_def2(int c, int a, int b)
_(requires c == 0 || c == 1)
_(ensures abs_choose(c, a, b) == ((c * a) + ((1 - c) * b)))
_(lemma) _(pure)
{
  if (c == 0){
  }else{
    _(assert c == 1)
  }
}


#endif // __SECC

#if __SECC
int toint(bool b);
_(ensures result == abs_toint(b))

void abs_choose_eq(int c, int a, int b)
  _(requires c == 0 || c == 1)
  _(ensures abs_choose(c,a,b) == a || abs_choose(c,a,b) == b)
  _(pure) _(lemma)
{
  if (c == 0){
  }else{
    _(assert c == 1)
  }
}

void max_abs_choose(int a, int b)
  _(ensures abs_choose(abs_toint(a>b),a,b) >= a &&
            abs_choose(abs_toint(a>b),a,b) >= b)
  _(pure) _(lemma)
{
  if (a > b){
    _(assert abs_toint(a>b) == 1)
  }else{
    _(assert abs_toint(a>b) == 0)    
  }    
}

void min_abs_choose(int a, int b)
  _(ensures abs_choose(abs_toint(a<b),a,b) <= a &&
            abs_choose(abs_toint(a<b),a,b) <= b)
  _(pure) _(lemma)
{
  if (a < b){
    _(assert abs_toint(a<b) == 1)
  }else{
    _(assert abs_toint(a<b) == 0)    
  }    
}

#else
#define toint(x) (x)
#endif // __SECC

int choose_ct(int c, int a, int b)
  _(requires c == 0 || c == 1)
  _(ensures result == abs_choose(c, a, b))
  _(ensures result == a || result == b)
{
  
  _(apply abs_choose_def2(c, a, b);)
  return ((c * a) + ((1 - c) * b));
}


int not(int a)
  _(requires a == 0 || a == 1)
  _(ensures result <=> (a == 0))
  _(ensures result == 0 || result == 1)
{
  return (1 - a);
}

int max_ct(int a, int b)
  _(ensures result >= a && result >= b &&
    (result == a || result == b))
{
  int t = toint(a>b);
  int max = choose_ct(t,a,b);
  _(apply max_abs_choose(a,b);)
  _(apply abs_choose_eq(t,a,b);)
  return max;
}

/* constant-time minimum as variant of constant-time max */
int min_ct(int a, int b)
  _(ensures result <= a && result <= b &&
    (result == a || result == b))
{
  int t = toint(a<b);
  int min = choose_ct(t,a,b);
  _(apply min_abs_choose(a,b);)
  _(apply abs_choose_eq(t,a,b);)
  return min;
}


/* constant-time memory comparison: compares n locations in p1 and p2.
   returns 0 iff they are equal. Non-zero otherwise. Result guaranteed to
   be >= 0. */
int memcmp_ct(int *p1, int *p2, int n)
  _(requires exists list<int> s1. ar(p1; n, s1))
  _(requires exists list<int> s2. ar(p2; n, s2))
  _(requires n :: low && n >= 0)
  // XXX: note the following gives us an error when encoding to SMT
  // I believe the error is caused somehow because == is interpreted as
  // polymorphic on lists, so we specialise it via list_eq
  //_(ensures (result == 0) <=> (s1 == s2))
  _(ensures (result == 0) <=> list_eq(s1,s2))
  _(ensures result == 0 || result == 1)
  _(ensures ar(p1; n, s1))
  _(ensures ar(p2; n, s2))  
{  
  if (n != 0){    
    _(unfold ar(p1; n, s1))
    _(unfold ar(p2; n, s2))
    _(assert exists int hd1, list<int> tl1. s1 == cons(hd1,tl1) && ar(p1+1;n-1,tl1))
    _(assert exists int hd2, list<int> tl2. s2 == cons(hd2,tl2) && ar(p2+1;n-1,tl2))


    int a = *p1;
    int b = *p2;

    // XXX: SecC's type checking gives problems with a != b here.
    //int c = (a != b);
    int c = toint(a != b);
    int d = memcmp_ct(p1+1,p2+1,n-1);
    int m = max_ct(c,d);

    //printf("n: %d, a: %d, b: %d, c: %d, d: %d, m: %d\n",n,a,b,c,d,m);
    _(assert list_eq(tl1,tl2) == (tl1 == tl2))

    _(fold ar(p1; n, s1))
    _(fold ar(p2; n, s2))
    return m;
  }else{
    _(apply { ar_zero_nil(p1,s1); ar_zero_nil(p2,s2); })    
    return 0;
  }
}

_(function int abs_max(int a, int b))

_(rewrites
  forall int a, int b. abs_max(a,b) == (a >= b ? a : b))

void max_is_abs_max(int m, int a, int b)
_(requires (m == a) || (m == b))
_(requires m >= a && m >= b)
_(ensures m == abs_max(a,b))
_(lemma) _(pure)
{
  if (m == a){
    _(assert a >= b)
  }else{
    _(assert m == b)
    _(assert b >= a)
    if (b > a){
    }else{
      _(assert a == b)
    }
  }
}

_(function int abs_max_list(list<int> l))
_(rewrites
  forall int hd. abs_max_list(cons(hd,nil)) == hd;
  forall int hd, int tlhd, list<int> tl. abs_max_list(cons(hd,(cons(tlhd,tl)))) == abs_max(hd,abs_max_list(cons(tlhd,tl))))

int max_list(int *p, int n)
  _(requires exists list<int> s. ar(p; n, s))
  _(requires n :: low && n > 0)
  _(ensures ar(p; n, s))
  _(ensures result == abs_max_list(s))
{
  if (n == 1){
    _(unfold ar(p; n, s))
    _(assert exists int _hd, list<int> _tl. s == cons(_hd,_tl))
    _(apply ar_zero_nil(p+1,_tl);)
    int res =  *p;      
    _(fold ar(p; n, s))
    return res;
  }else{
    _(unfold ar(p; n, s))
    _(assert exists int _hd, list<int> _tl. s == cons(_hd,_tl))
    _(apply ar_nonzero_cons(p+1,n-1,_tl);)
    int m = max_list(p+1, n-1);
    int res = max_ct(*p,m);
    _(apply max_is_abs_max(res,_hd,m);)
    _(fold ar(p; n, s))    
    return res;
  }
}

  
/* Given a password guess and a stored password (where the guess is at least as long as the stored password), 
   the constant-time comparison can be used to compare the two in which case it leaks no more than whether the
   two passwords are equal */
int password_checker(int *guess, int *stored_password, int n)
  _(requires exists list<int> _guess. ar(guess; n, _guess))
  _(requires exists list<int> _storedpw. ar(stored_password; n, _storedpw))
  _(requires (_guess == _storedpw) :: low)
  _(requires n :: low && n >= 0)
  _(ensures result :: low)
  _(ensures ar(guess; n, _guess))
  _(ensures ar(stored_password; n, _storedpw))
{
  int r = memcmp_ct(guess, stored_password, n);

  /* needed to get reason that the result is low, since the precondition
     uses the equality rather than list_eq */
  _(assert list_eq(_guess, _storedpw) == (_guess == _storedpw))

  return r;
}
