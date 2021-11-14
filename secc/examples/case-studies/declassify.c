#include "secc.h"

/* examples concerning declassification policies in SecC. */

/* Introduction */

/* SecC supports interesting declassification policy reasoning via "assume".
   For instance: */
int declassify(int x, int y)
  _(requires x :: low)
  _(requires y == 0 :: low)
  _(ensures result :: low)
{
  int z = x + y;
  if (z != x){
    _(assume y :: low)
  }
  return z;
}

/* Motivating Example: confirmed declassification */

/* Let us consider 'confirmed declassification'  in which we want to ask
   the user for permission to declassify a value and only declassify it if
   the user agrees.  See e.g. Schoepe et al., CSF'20 */

int ask_user1(int x);
_(ensures result :: low)
_(ensures result ==> x :: low)

int do_declassify1(int x)
_(ensures result :: low)
_(ensures result == x || result == 0)
{
  int r = 0;
  if (ask_user1(x)){
    r = x;
  }
  return r;
}


/* This is nice in that there is no way to 'get it wrong' and accidentally
   have the program release the wrong value (i.e. one that wasn't 
   declassified). But it isn't clear what the above "means". Let's rewrite
   it with an 'assume' statement to make the meaning clearer.
*/

int ask_user2(int x);
_(ensures result :: low)

int do_declassify2(int x)
_(ensures result :: low)
_(ensures result == x || result == 0)
{
  int r = 0;
  int b = ask_user2(x);
  _(assume b ==> x :: low)
  if (b){
    r = x;
  }
  return r;
}

/* Now the meaning is clear: when ask_user(x) returns true, we are willing to
   assume that the low attacker knows x. 

   The problem of course is that it is very easy to misuse 'assume'. How can
   we get the benefits of both approaches: making it clear what is being
   assumed but not allowing it to be misused? */

/* A solution: we will use abstract predicates/functions and impose 
   easily checkable static conventions on 'assume' statements to make sure
   they cannot be misused.  */

/* We use this to represent a permission to declassify a value */

/* this is an abstract function rather than an abstract predicate so that we
   can put it on the LHS of an ==> etc. Also no reason that it should not
   be freely duplicable, etc. */
_(function bool safe_to_declassify(int x))

/* Then 'ask_user' is specified to give us one of these permissions but
   only when the user grants it. */
int ask_user(int x);
_(ensures result :: low)
_(ensures result ==> safe_to_declassify(x))

/* for the assume statement, we incorporate explicitly checking the permission
   to justify the assumption. Together these make clear what we are assuming
   (declassifying) and precisely under what conditions. */
int do_declassify(int x)
_(ensures result :: low)
_(ensures result == x || result == 0)
{
  int r = 0;
  if (ask_user(x)){
    _(assume safe_to_declassify(x) ==> x :: low)
    r = x;
  }
  return r;
}

/* Trivial example showing failure when we haven't obtained the permission */
int do_declassify_without_asking(int x)
_(ensures result :: low)
_(ensures result == x || result == 0)
_(fails insecure)
{
  int r = 0;
  _(assume safe_to_declassify(x) ==> x :: low)
  r = x;
  
  return r;
}

/* Example highlighting that our logic is one of partial correctness */
int declassify_by_attrition(int x)
_(ensures result :: low)
_(ensures result == x)
{
  while (!ask_user(x)){
  }
  
  _(assume safe_to_declassify(x) ==> x :: low)
   return x;
}


/* now the above is not very declarative. Can we do better?

   The policy is: send an output and atomically receive an input.
   If the input you got was positive then the output is safe to 
   declassify.

   Let us encode that over I/O traces, each of whose elements look like:
*/
struct pair {
  int value;
  int safe_to_declass;
};
typedef struct pair pair_t;

/* tracks the trace of I/O actions that have occurred so far */
_(predicate io_trace(;list<pair_t> xs))

/* an extensional spec of the declassification policy, allowing only
   the most recently confirmed value to be declassified  */
// XXX: moving this definition below ask_user3 causes a parse error
_(predicate safe_to_declassify2(;int x)
  (exists int r, pair_t io, list<pair_t> ios. io_trace(;cons(io,ios)) &&
   io.value == x && io.safe_to_declass == r && r))


/* this now has a specification in terms of just its I/O */
int ask_user3(int x);
_(requires exists list<pair_t> xs. io_trace(;xs))
_(ensures exists pair_t e. io_trace(;cons(e,xs)) &&
    e.value == x && e.safe_to_declass == result && result :: low)

/* finally, we have to manually check that the security policy holds
   before doing the assume, which again can be checked easily statically */
int do_declassify3(int x)
_(requires exists list<pair_t> xs. io_trace(;xs))
_(ensures result :: low)
_(ensures result == x || result == 0)
_(ensures exists list<pair_t> xs. io_trace(;xs))
{
  int r = 0;
  int res = ask_user3(x);
  if (res){
    _(fold safe_to_declassify2(;x))
    _(assume x :: low)
    r = x;
    _(unfold safe_to_declassify2(;x))
  }
  return r;
}



/* Running average example (Schoepe et al. CSF 2020):
   the policy allows current average of inputs consumed so far 
   (by one thread) to be declassified (by another thread) so long as 
   we have consumed 'min' amount, where 'min' is a lock-protected shared 
   variable that is updated by another thread.

   The code uses shared variables 'sum' and 'count' to track respectively
   the sum of values input so far and the number of values input so far.

   Here we use a single lock to protect access to all of the shared state.
   TODO: consider splitting into multiple locks as per the CSF paper 
*/
struct avg_state {
  int count;
  int sum;
  int min;
};


/* remembers the inputs consumed so far */
_(predicate consumed_inputs(;list<int> inps))

/* holds when s and c correctly track the sum and count of the inputs
   consumed so far */
_(predicate avg_state_correct(;int s, int c, list<int> xs)
  xs == nil :: low && (xs == nil ? s == 0 && c == 0 :
                       (exists int y, list<int> ys. xs == cons(y,ys) && avg_state_correct(;s-y,c-1,ys))))

_(function int length(list<int> xs))

_(rewrites
	length(nil) == 0;
	forall int x, list<int> xs. length(cons(x,xs)) == 1 + length(xs))



_(function int ssum(list<int> xs))

_(rewrites
	ssum(nil) == 0;
	forall int x, list<int> xs. ssum(cons(x,xs)) == x + ssum(xs))

_(predicate avg_state_correct2(;int s, int c, list<int> xs)
  c :: low && c == length(xs) && s == ssum(xs))


void length_nonnegative(list<int> xs)
_(ensures length(xs) >= 0)
_(lemma) _(pure)
{
  if (xs == nil){
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    length_nonnegative(ys);
  }
}

void length_zero_nil(list<int> xs)
_(requires length(xs) == 0)
_(ensures xs == nil)
_(lemma) _(pure)
{
  if (xs == nil){
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    length_nonnegative(ys);
    _(assert length(xs) > 0)
  }
}

void length_nonzero_cons(list<int> xs)
_(requires length(xs) != 0)
_(ensures exists int y, list<int> ys. xs == cons(y,ys))
_(lemma) _(pure)
{
  if (xs == nil){
    _(assert length(xs) == 0)
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
  }
}

void length_low_nil_low(list<int> xs)
_(requires length(xs) :: low)
_(ensures xs == nil :: low)
_(lemma)
{
  if (length(xs) == 0){
    length_zero_nil(xs);
  }else{
    length_nonzero_cons(xs);
  }
}

void avg_state_correct_implies(int s, int c, list<int> xs)
_(requires avg_state_correct(;s,c,xs))
_(ensures avg_state_correct2(;s,c,xs))
_(lemma)
{
  _(unfold avg_state_correct(;s,c,xs))
  if (xs == nil){
    _(fold avg_state_correct2(;s,c,nil))
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    _(apply avg_state_correct_implies(s-y,c-1,ys);)
    _(unfold avg_state_correct2(;s-y,c-1,ys))
    _(fold avg_state_correct2(;s,c,xs))      
  }
}

void avg_state_correct2_implies(int s, int c, list<int> xs)
_(requires avg_state_correct2(;s,c,xs))
_(ensures avg_state_correct(;s,c,xs))
_(lemma) 
{
  _(unfold avg_state_correct2(;s,c,xs))
  length_low_nil_low(xs);
  if (xs == nil){
    _(fold avg_state_correct(;s,c,nil))
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
      
    // little bit annoying deriving length(ys) :: low
    _(assert length(xs) == length(cons(y,ys)))
    _(assert length(xs) == 1 + length(ys))      

    _(fold avg_state_correct2(;s-y,c-1,ys))
    avg_state_correct2_implies(s-y,c-1,ys);
    _(fold avg_state_correct(;s,c,xs))      
  }
}

/* the invariant protected by the lock */
_(predicate avg_inv(struct avg_state *st)
  exists int c, int s, int m, list<int> inps. consumed_inputs(;inps) &&
  &st->count |-> c && c :: low && c >= 0 &&
  &st->sum |-> s && &st->min |-> m && m > 0 && m :: low &&
  avg_state_correct(;s, c, inps)  
)

/* The security policy. */
_(predicate avg_safe_to_declassify(int x, struct avg_state *st; list<int> inps)
  exists int c, int s, int m. consumed_inputs(;inps) &&
  c :: low && c == length(inps) && s == ssum(inps) &&
  &st->min |-> m && m > 0 && m :: low &&
  x == (s / c) && c > m
)

/* lock acquisition produces the invariant */
struct avg_state * avg_lock();
_(ensures avg_inv(result))

/* lock release consumes the invariant */
void avg_unlock(struct avg_state *st);
_(requires avg_inv(st))

/* axiomatise the function for getting the next input */
int avg_get_input();
_(requires exists list<int> inps. consumed_inputs(;inps))
_(ensures  consumed_inputs(;cons(result,inps)))


void sum_lemma(int s, int c, list<int> xs, int x)
_(lemma)
_(requires avg_state_correct(;s, c, xs))
_(ensures avg_state_correct(;s+x, c+1, cons(x,xs)))
{
  _(fold avg_state_correct(;s+x,c+1,cons(x,xs)))    
}

/* the thread that reads, counts and sums the inputs */
void avg_sum_thread(){
  struct avg_state * st = avg_lock();
  _(unfold avg_inv(st))
  _(assert exists list<int> inps. consumed_inputs(;inps))
  int i = avg_get_input();
  _(apply sum_lemma(st->sum, st->count, inps, i);)
  st->count += 1;
  st->sum += i;
  _(fold avg_inv(st))  
  avg_unlock(st);
}

/* the thread that increments the 'min' variable */
void avg_inc_min_thread(){
  struct avg_state * st = avg_lock();
  _(unfold avg_inv(st))
  st->min += 1;
  _(fold avg_inv(st))  
  avg_unlock(st);
}

/* not true at present
void avg_safe_to_declassify_implies_avg_inv(int avg, struct avg_state *st)
_(requires avg_safe_to_declassify(avg,st))
_(ensures avg_inv(st))
_(lemma)
{
  _(unfold avg_safe_to_declassify(avg,st))
  _(fold avg_inv(st))
}
*/

/* the thread that does the declassification */
void avg_declass_thread(){
  struct avg_state * st = avg_lock();
  _(unfold avg_inv(st))
    _(assert exists list<int> inps. consumed_inputs(;inps))
  if (st->count > st->min){
    int avg = st->sum / st->count;
    _(assert  consumed_inputs(;inps))
    _(assert exists int c, int s. &st->sum |-> s && &st->count |-> c)
    _(apply avg_state_correct_implies(s, c, inps);)
    _(unfold avg_state_correct2(;s, c, inps))
      
    _(fold avg_safe_to_declassify(avg,st;inps))
    _(assume (avg :: low))
      
    _(unfold avg_safe_to_declassify(avg,st;inps))
    _(fold avg_state_correct2(;s, c, inps))
    _(apply avg_state_correct2_implies(s, c, inps);)
    _(fold avg_inv(st))
  }else{
    _(fold avg_inv(st))
  }
  avg_unlock(st);
}


