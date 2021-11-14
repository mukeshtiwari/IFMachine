#include "secc.h"

/* here we use SecC to specify some confidentiality properties of some
   query-style functions. For simplicity, we consider associative arrays
   that store (key,value) pairs. Each array may contain multiple elements
   that share a common key. We use SecC's value-dependent classification
   assertions to specify that query operations should return only derived
   only from those values associated with the given key. 
*/
typedef struct {
  int key;
  int value;
} elem_t;


/* We axiomatize the existence of an injective function that, for each key
 * k associates it with a unique security label label(k).
*/
_(function sec label(int x))
_(axioms
  forall int i, int j. label(i) == label(j) ==> i == j)

/* An array of elems of length n storing  arbitrary values.
 * Describes the empty heap region if n <= 0 */
_(predicate ar(elem_t *a, int n)
  n > 0 ==> exists int k, int v. &a->key |-> k && &a->value |-> v && ar(a + 1, n - 1))

/* An key/value array all of whose values have the security level associated
 * with their key. */
_(predicate ar_sec(elem_t *a, int n)
  n > 0 ==> exists int k, int v. &a->key |-> k && &a->value |-> v && k :: low && v :: label(k) && ar_sec(a + 1, n - 1))


int SUCCESS = 0;
int FAILURE = 1;

void ar_sec_snoc(elem_t *a, int n)
_(requires n >= 0)
_(requires n :: low)
_(requires ar_sec(a,n))
  _(requires exists int k, int v. &(a+n)->key |-> k && &(a+n)->value |-> v && k :: low && v :: label(k))
_(ensures ar_sec(a,n+1))
_(lemma)
{
  if (n == 0){
    _(unfold ar_sec(a,n))
    _(fold ar_sec(a+1,0))
    _(fold ar_sec(a,1))
  }else{
    _(unfold ar_sec(a,n))
    _(apply ar_sec_snoc(a+1,n-1);)
    _(fold ar_sec(a,n+1))
  }
}

void ar_sec_join(elem_t *a, int n, int m)
_(requires n >= 0 && m >= 0)
_(requires n :: low && m :: low)
_(requires ar_sec(a,n) && ar_sec(a+n,m))
_(ensures ar_sec(a,n+m))
_(lemma)
{
  if (n == 0){
    _(unfold ar_sec(a,n))
  }else{
    _(unfold ar_sec(a,n))
    _(apply ar_sec_join(a+1,n-1,m);)
    _(fold ar_sec(a,n+m))
  }
}


/* returns SUCCESS/FAILURE. On SUCCESS *valueOut holds the value corresponding
 * to the given key. The code is a little awkward becuase we don't yet
 * support return statements in loop bodies */
int lookup(elem_t *elems, int len, int key, int *valueOut)
  _(requires ar_sec(elems,len))
  _(requires len :: low)
  _(requires key :: low)
  _(requires len >= 0)
  _(requires exists int oldOut. valueOut |-> oldOut)
  _(ensures exists int out. valueOut |-> out)
  _(ensures result == SUCCESS ==> out :: label(key))
  _(ensures result == FAILURE ==> out == oldOut)
  _(ensures result == SUCCESS || result == FAILURE)
  _(ensures ar_sec(elems,len))
{
  int i = 0;
  elem_t *p = elems;
  int ret = FAILURE;
  _(fold ar_sec(elems,0))
  while (i < len && ret == FAILURE)
    _(invariant i >= 0 && i <= len)
    _(invariant ret :: low && i :: low)
    _(invariant ret == SUCCESS ==> exists int v. valueOut |-> v && v :: label(key)) 
    _(invariant ret == FAILURE ==> valueOut |-> oldOut)
    _(invariant ret == SUCCESS || ret == FAILURE)
    _(invariant ret >= SUCCESS && ret <= FAILURE)
    _(invariant ar_sec(p,len-i))
    _(invariant ar_sec(elems,i))
    _(invariant p == elems + i)
    {
    _(unfold ar_sec(p,len - i))
    if (p->key == key){
      *valueOut = p->value;
      ret = SUCCESS;
    }
    p++;
    _(apply ar_sec_snoc(elems,i);)    
    i++;
  }
  _(apply ar_sec_join(elems,i,len-i);)
  return ret;
}

void split(elem_t *a, int i, int n)
  _(lemma)
	_(requires i :: low)
    _(requires 0 <= i && i <= n)
    _(requires ar_sec(a, n))
    _(ensures  ar_sec(a, i) && ar_sec(a + i, n - i))
{
	if(i == 0) {
          _(fold ar_sec(a, 0))
	} else {
          _(unfold ar_sec(a, n))
          _(apply split(a+1, i-1, n-1);)
          _(fold ar_sec(a, i))
	}
}

void expose(elem_t *a, int i, int n)
    _(lemma)
	_(requires i :: low)
    _(requires 0 <= i && i < n)
     _(requires ar_sec(a, n))
     _(ensures  exists int k, int v. &(a + i)->key |-> k && &(a + i)->value |-> v && k :: low && v :: label(k))
     _(ensures  ar_sec(a, i) && ar_sec(a + i + 1, n - i - 1))
{
	if(i == 0) {
          _(unfold ar_sec(a, n))
          _(fold ar_sec(a, 0))
	} else {
	  _(unfold ar_sec(a, n))
          _(apply expose(a+1, i-1, n-1);)
          _(fold ar_sec(a, i))
	}
}

void cover(elem_t *a, int i, int n)
    _(lemma)  
	_(requires i :: low)
    _(requires 0 <= i && i < n)
     _(requires ar_sec(a, i) && ar_sec(a + i + 1, n - i - 1))
     _(requires exists int k, int v. &(a + i)->key |-> k && &(a + i)->value |-> v && k :: low && v :: label(k))
     _(ensures  ar_sec(a, n))
{
	if(i == 0) {
          _(unfold ar_sec(a, 0))
          _(fold   ar_sec(a, n))
	} else {
	  _(unfold ar_sec(a, i))
          _(apply cover(a+1, i-1, n-1);)
          _(fold ar_sec(a, n))
	}
}

/* the same spec holds for binary search */
int binsearch(elem_t *elems, int len, int key, int *valueOut)
  _(requires ar_sec(elems,len))
  _(requires len :: low)
  _(requires key :: low)
  _(requires exists int oldOut. valueOut |-> oldOut)
  _(ensures exists int out. valueOut |-> out)
  _(ensures result :: low)
  _(ensures result == SUCCESS || result == FAILURE)
  _(ensures result == SUCCESS ==> out :: label(key))
  _(ensures result == FAILURE ==> out == oldOut)
  _(ensures ar_sec(elems,len))
{
  if (len <= 0){
    return FAILURE;
  }
  int mid = len/2;
  _(apply expose(elems,mid,len);)

  int k = (elems + mid)->key;
  if (k == key){
    *valueOut = (elems + mid)->value;
    _(apply cover(elems,mid,len);)
    return SUCCESS;
  }else{
    if (len == 1){
      _(apply cover(elems,mid,len);)      
      return FAILURE;
    }
    if (k > key){
      _(apply cover(elems,mid,len);)
      _(apply split(elems,mid-1,len);)
      int ret = binsearch(elems,mid-1,key,valueOut);
      _(apply ar_sec_join(elems,mid-1,len-(mid-1));)
      return ret;
    }else{
      _(apply cover(elems,mid,len);)
      _(apply split(elems,mid+1,len);)
      int ret = binsearch(elems+mid+1,len - mid - 1,key,valueOut);
      _(apply ar_sec_join(elems,mid+1,len-(mid+1));)
      return ret;
    }
  }
}

int sum_all(elem_t *elems, int len, int key)
  _(requires ar_sec(elems,len))
  _(requires len :: low)
  _(requires key :: low)
  _(requires len >= 0)
  _(ensures result :: label(key))
  _(ensures ar_sec(elems,len))
{
  int sum = 0;
  elem_t *p = elems;
  int i = 0;
  _(fold ar_sec(elems,0))
  while (i < len)
    _(invariant i >= 0 && i <= len)
    _(invariant sum :: label(key) && i :: low)
    _(invariant ar_sec(p,len-i))
    _(invariant ar_sec(elems,i))
    _(invariant p == elems + i)
    {
    _(unfold ar_sec(p,len - i))
    if (p->key == key){
      sum += p->value;
    }
    p++;
    _(apply ar_sec_snoc(elems,i);)    
    i++;
  }
  _(apply ar_sec_join(elems,i,len-i);)
  return sum;
}


/* returns the sum of all values associated to the given key. 0 otherwise
   this shows in some sense the ease of the recursive reasoning. */
int sum_all_rec(elem_t *p, int len, int key, int init)
  _(requires ar_sec(p,len))
  _(requires init :: label(key))
  _(requires len :: low)
  _(requires len >= 0)
  _(requires key :: low)
  _(ensures ar_sec(p,len))
  _(ensures result :: label(key))
{
  if (len > 0)
  {
    _(unfold ar_sec(p,len))
    if (p->key == key){
      int s = sum_all_rec(p+1,len-1,key,init + p->value);
      _(fold ar_sec(p,len))
      return s;
    }else{
      int s = sum_all_rec(p+1,len-1,key,init);
      _(fold ar_sec(p,len))
      return s;
    }
  }else{
    return init;
  }
}

void remove_all(elem_t *elems, int len, int key)
  _(requires ar_sec(elems,len))
  _(requires len :: low && key :: low && len >= 0)
  _(ensures ar_sec(elems,len))
{
  int i = 0;
  elem_t *p = elems;
  _(fold ar_sec(elems,0))
  while (i < len)
    _(invariant i :: low && i >= 0 && i <= len)
    _(invariant ar_sec(elems,i))
    _(invariant ar_sec(p,len-i))
    _(invariant p == elems + i)
  {
    _(unfold ar_sec(p,len-i))
    if (p->key == key){
      p->value = 0;
    }
    _(apply ar_sec_snoc(elems,i);)
    p++;
    i++;
  }
  _(unfold ar_sec(p,len-i))
}

