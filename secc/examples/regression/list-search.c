#include "secc.h"


enum ret_code 
{
  Failure,
  Success
};
typedef enum ret_code status_code;

_(function
	list<int> append(list<int> xs, list<int> ys))

_(rewrites
	forall list<int> ys. 
    append(nil, ys) == ys;
	forall int x, list<int> xs, list<int> ys.
		append(cons(x,xs), ys) == cons(x, append(xs, ys)))

// This lemma is not used anywhere in this file (proof)
void append_associative(list<int> xs, list<int> ys, list<int> zs)
_(requires xs :: low)
_(ensures  append (xs, append(ys, zs)) ==  append(append (xs, ys), zs))
_(lemma)
{
  if (xs == nil)
  {
    _(assert append(nil, append(ys, zs)) == append(append(nil, ys), zs))
    return;
  }
  else 
  {
    _(assert exists int t, list<int> ts. xs == cons(t, ts))
    append_associative(ts, ys, zs);
    return;
  }

}

_(function status_code search(int t, list<int> xs)) 

_(rewrites 
  forall int t. search(t, nil) == Failure;
  forall int t, int x, list<int> xs.
    search(t, cons(x, xs)) ==  
    ((t == x) ? Success : search(t, xs)))

void search_proof(int t, list<int> xs)
_(requires xs :: low)
_(requires t :: low)
_(requires search(t, xs) == Success)
_(ensures exists int p, list<int> ll, list<int> rr.
    xs == append(ll, cons(p, rr)) && p == t)
_(lemma)
{
  if(xs == nil)
  {
      _(assert search(t, nil) == Failure)
      return;
  }
  else 
  {
    _(assert exists int y, list<int> ys. xs == cons(y, ys))
    if(y == t)
    {
        // We have found an element at the front of the list
         _(assert y == t)
         _(assert search(t, cons(y, ys)) == Success)
         _(assert xs == append(nil, cons(y, ys)))
         return;
         
    }
    else  
    {
      _(assert y != t)
      _(assert search(t, cons(y, ys)) == search (t, ys))
      search_proof(t, ys);
      _(assert search(t, ys) == Success ==> 
        exists int x, list<int> l, list<int> r. ys == append(l, cons(x, r)) && 
        xs == append (cons(y, l), cons (x, r)) && (x == t) )
      return;
    
    }
   
  }
  
}
