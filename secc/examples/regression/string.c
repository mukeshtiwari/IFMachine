#include "secc.h"

/* a string of length n whose elements have classification lev */
_(predicate str(char *a, sec lev; int n)
  n == 0 ? a |-> 0 : n > 0 && exists char x. a |-> x && x != 0 && x :: lev && str(a + 1, lev; n - 1))

/* a partial (non-terminated) string of length n */
_(predicate pstr(char *a, sec lev, int n)
  n > 0 ==> exists char x. a |-> x && x != 0 && x :: lev && pstr(a + 1, lev, n - 1))


void pstr_snoc(char *a, sec lev, int n)
_(requires n >= 0)
_(requires n :: low)
_(requires pstr(a,lev,n))
_(requires exists char x. a+n |-> x && x != 0 && x :: lev)
_(ensures pstr(a,lev,n+1))
_(lemma)
{
  if (n == 0){
    _(unfold pstr(a,lev,n))
    _(fold pstr(a+1,lev,0))
    _(fold pstr(a,lev,1))
  }else{
    _(unfold pstr(a,lev,n))
    _(apply pstr_snoc(a+1,lev,n-1);)
    _(fold pstr(a,lev,n+1))
  }
}

void pstr_str(char *s1, sec lev, int n, int m)
  _(requires pstr(s1,lev,n) && str(s1+n,lev;m))
  _(requires n :: low && m :: low && n >= 0 && m >= 0)
  _(ensures str(s1,lev;n+m))
  _(lemma)
{
  if (n == 0){
    _(unfold pstr(s1,lev,n))
  }else{
    _(unfold pstr(s1,lev,n))
    _(apply pstr_str(s1+1,lev,n-1,m);)
    _(fold str(s1,lev;n+m))
  }
}

/* predicate for string equality */
_(predicate streq(char *s1, char *s2, int n)
  (n > 0 ==> (exists char x. s1 |-> x && s2 |-> x && streq(s1+1,s2+1,n-1))))

void streq_snoc(char *s1, char *s2, int n)
  _(lemma)
  _(requires streq(s1,s2,n) && n :: low && n >= 0)
  _(requires exists char x. s1+n |-> x && s2+n |-> x)
  _(ensures streq(s1,s2,n+1))
{
  if (n == 0){
    _(unfold streq(s1,s2,n))
    _(fold streq(s1+1,s2+1,0))
    _(fold streq(s1,s2,1))
  }else{
    _(unfold streq(s1,s2,n))
    _(apply streq_snoc(s1+1,s2+1,n-1);)
    _(fold streq(s1,s2,n+1))
  }
}

/* returns 0 when strings are equal
   TODO: specify correctness of return value. At present we avoid doing so
         as it requires use of e.g. streq above which overlaps with the
         str postconditions. What we really need is support for sequences
         as predicate arguments. */
int strcmp(char *s1, char *s2)
_(requires exists int n1, int n2. str(s1,low;n1) && str(s2,low;n2) && n1 :: low && n2 :: low && n1 >= 0 && n2 >= 0)
_(ensures str(s1,low;n1) && str(s2,low;n2))
{
  /* XXX: for some reason we cannot mention "low" in _(apply ...) */
  _(assert exists sec lev. lev == low)      
    
  char *p = s1;
  char *q = s2;
  int ret = 0;
  int done = 0;
  int len1 = 0;
  int len2 = 0;
  _(fold pstr(s1,low,0))
  _(fold pstr(s2,low,0))
  while (ret == 0 && !done)
    _(invariant n1 >= 0 && n2 >= 0)
    _(invariant (ret == 0) :: low)
    _(invariant str(p,low;n1 - len1))
    _(invariant str(q,low;n2 - len2))
    _(invariant len1 :: low && len2 :: low && done :: low)
    _(invariant done != 0 ==> (len1 == n1 && len2 == n2))
    _(invariant pstr(s1,low,len1) && pstr(s2,low,len2))
    _(invariant p == s1 + len1 && q == s2 + len2)
    _(invariant len1 >= 0 && len1 <= n1 && len2 >= 0 && len2 <= n2)
  {
    _(unfold str(p,low;n1 - len1))
    _(unfold str(q,low;n2 - len2))
    ret = (*p - *q);
    if (*p == 0 && *q == 0){
      done = 1;
      _(fold str(p,low;n1 - len1))
      _(fold str(q,low;n2 - len2))        
    }else{
      if (*p != 0) {
        p++;
        _(apply pstr_snoc(s1,lev,len1);)
        len1++;
      } else {
        _(fold str(p,low;n1 - len1))
      }
      if (*q != 0) {
        q++;
        _(apply pstr_snoc(s2,lev,len2);)
        len2++;
      } else {
        _(fold str(q,low;n2 - len2))
      }
    }
  }
  _(apply pstr_str(s1,lev,len1,n1-len1);)
  _(apply pstr_str(s2,lev,len2,n2-len2);)
  return ret;
}


    

  
