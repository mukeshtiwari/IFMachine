#include "secc.h"

_(function int length(list<int> ios))

_(rewrites
  length(nil) == 0;
  forall int x, list<int> xs.length(cons(x, xs)) == 1 + length(xs))

_(predicate length_is_low(;list<int> ios)
  (ios == nil :: low) &&
  (ios == nil ? true :  (exists int e, list<int> es. ios == cons(e, es) && length_is_low(;es))))

void length_nonnegative(list<int> xs)
_(ensures length(xs) >= 0)
_(pure) _(lemma)
{
  if(xs != nil) {
    _(assert exists int y, list<int> ys. xs == cons(y, ys))
      length_nonnegative(ys);
  }
}

void length_zero_is_nil(list<int> xs)
  _(requires length(xs) == 0)
  _(ensures xs == nil)
  _(pure) _(lemma)
{
  if (xs == nil){
    return;
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    length_nonnegative(ys);
    _(assert length(cons(y,ys)) > 0)
  }
}

void length_low_eq_nil_low(list<int> xs)
  _(requires length(xs)::low)
  _(ensures (xs == nil)::low)
  _(lemma)
{
  _(apply
    if(length(xs) == 0){
      length_zero_is_nil(xs);
    }else{
      _(assert length(xs) != 0)
      _(assert length(nil) == 0)
      _(assert xs != nil)
    }
  )
}

void length_low_length_is_low(list<int> ios)
  _(requires length(ios)::low)
  _(ensures length_is_low(;ios))
  _(lemma)
{
  length_low_eq_nil_low(ios);
  if(ios == nil){
    _(fold length_is_low(;ios))
  }else{
    _(assert exists int y, list<int> ys. ios == cons(y,ys))
    _(assert length(ios) == 1 + length(ys))
    length_low_length_is_low(ys);
    _(fold length_is_low(;cons(y,ys)))
  }
}
