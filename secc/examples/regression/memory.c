int *alloc();
	_(ensures exists int v. result |-> v)

void free(int *x);
	_(requires exists int v. x |-> v)

int deref(int *p)
	_(requires exists int v. p |-> v)
	_(ensures p |-> v)
	_(ensures result == v)
{
	return *p;
}


void test_eq(int *x, int *y)
	_(requires x == y)
	_(requires exists int v. x |-> v)
	_(ensures  y |-> v)
{
}

void disjoint(int *p, int *q)
	_(maintains exists int v, int w. p |-> v && q |-> w)
	_(ensures p != q)
{
  // we need to assert the disjointness explicitly
  _(assert p != q)
}

struct pair {
	int fst;
	int snd;
};

void disjoint_pair(struct pair *p)
	_(maintains exists int v, int w. &p->fst |-> v && &p->snd |-> w)
	_(ensures &p->fst != &p->snd)
{
  _(assert &p->fst != &p->snd)
}

void disjoint_pair_incorrect(struct pair *p)
  _(ensures &p->fst != &p->snd)
  _(fails incorrect)
{
  // there is no precondition from which to derive disjointness
  _(assert &p->fst != &p->snd)
}

int aux()
	_(fails memory)
	_(ensures result == 0)
{
	int *p;
	_(assume exists int v. p |-> v)
	*p = 0;
	_(assert exists int v. p |-> v && v :: low())
	_(assert v == 0) // note: v is now bound to the value of *p
	return *p;
}

void calls_fail()
  _(fails memory)
{
  return aux();
}

void baz(int *p)
	_(maintains exists int v. p |-> v)
{
	_(assert exists int v. v == 0)
	_(assert v == 0)
}


/* tests for predicate consumption */
_(predicate inv(int *p) (exists int v. p |-> v))

_(predicate blah(int *l, int *p) (exists int _l. l |-> _l && (_l == 1 ==> inv(p))))


/* this should successfully pass. In particular, since l |-> 0, folding
   blah should not consume inv(p) */
void func(int *p, int * l)
_(requires inv(p))
_(requires exists int _lv. l |-> _lv && _lv :: low && _lv == 0)
_(ensures inv(p))
_(ensures blah(l,p))
{
  _(fold blah(l,p))
}

/* this should fail. In particular, since l |-> 0, folding
   blah should yield at least one state that is satisfiable in which
   inv(p) does not hold (because it never held in the precondition) */
void func3(int *p, int * l)
  _(requires exists int _lv. l |-> _lv && _lv :: low && _lv == 0)
  _(ensures inv(p))
  _(ensures blah(l,p))
  _(fails memory)
{
  _(fold blah(l,p))
}

/* this should fail. Because l |-> 1, folding blah should consume inv,
   meaning the postcondition cannot be satisfied */
void func2(int *p, int * l)
  _(requires inv(p))
  _(requires exists int _lv. l |-> _lv && _lv :: low && _lv == 1)
  _(ensures inv(p))
  _(ensures blah(l,p))
  _(fails memory)
{
  _(fold blah(l,p))
 }

int *alloc_int();
  _(ensures result :: low)
  _(ensures result != NULL ==> exists int v. result |-> v)

void free_int(int *p);
  _(requires exists int v. p |-> v)

void bad_alloc()
  _(fails memory)
{
  int *p = alloc_int();
  free_int(p);
}

void good_alloc(){
  int *p = alloc_int();
  if (p){
    *p = 5;
    free_int(p);
  }
}

void memory_leak()
  _(fails memory)
{
  int *p = alloc_int();
  if (p){
    *p = 5;
  }
}

struct node {
  int data;
  struct node *next;
};

typedef struct node node_t;

_(predicate lst(node_t *p)
  (p != null ==> exists int d, node_t *n. &(p->data) |-> d && &(p->next) |-> n && lst(n)))

node_t *alloc_node();
  _(ensures result :: low)
  _(ensures result != null ==> exists int d, node_t *n.  &(result->data) |-> d && &(result->next) |-> n)

void free_node(node_t *p);
  _(requires exists int d, node_t *n. &(p->data) |-> d && &(p->next) |-> n)

node_t *get_tl(node_t *p)
_(requires lst(p) && p != null)
_(ensures lst(result))
{
  node_t *n;
  _(unfold lst(p))
  n = p->next;
  free_node(p);
  return n;
}

node_t *cons(int d, node_t *p)
  _(requires lst(p))
  _(ensures lst(result))
{
  node_t *hd = alloc_node();
  if (hd){
    hd->data = d;
    hd->next = p;
    _(fold lst(hd))
    return hd;
  }else{
    // couldn't allocate memory, so just return the original list
    return p;
  }
}

/* test case for conditional proof strategies */
_(predicate ptr(int *p, sec l, int v)
  p |-> v && v :: l)

_(predicate ptr_sec(int *p, int lev, int v)
  lev :: low && (lev == 0 ==> ptr(p,low, v)))

void test_branching(int *p)
_(requires exists int lev, int v. ptr_sec(p, lev, v))
_(ensures ptr_sec(p, lev, v))
{
  _(unfold ptr_sec(p, lev, v))
  _(apply
    if(lev == 0) {
      _(unfold ptr(p,low, v))
      if (v > 0) {
        _(fold ptr(p,low, v))
      } else {
        _(fold ptr(p,low, v))
      }
    }
   )
  _(fold ptr_sec(p, lev, v))
}

/* Issue 15: bug in the parser */
typedef struct {
  int *data;        /* the backing memory */
} buf_t;

void get(buf_t *b, int i, int *out)
  _(requires exists int * _data. &b->data |-> _data)
  _(requires exists int x. _data + i |-> x)
  _(requires exists int _old. out |-> _old)
  _(ensures out |-> x)
  _(ensures &b->data |-> _data)
  _(ensures _data + i |-> x)
{
  *out = b->data[i];
}

/* Issue 13: loops and variable binding, now fixed */
_(predicate str(char *a; int n)
  n == 0 ? a |-> 0 : n > 0 && exists char x. a |-> x && x != 0 && str(a + 1; n - 1))

_(predicate pstr(char *a; int n)
  n > 0 ==> exists char x. a |-> x && x != 0 && pstr(a + 1; n - 1))

void pstr_snoc(char *a, int n)
_(requires n >= 0)
_(requires n :: low)
_(requires pstr(a;n))
_(requires exists char x. a+n |-> x && x != 0)
_(ensures pstr(a;n+1))
_(lemma)
{
  if (n == 0){
    _(unfold pstr(a;n))
      _(fold pstr(a+1;0))
      _(fold pstr(a;1))
      }else{
    _(unfold pstr(a;n))
      _(apply pstr_snoc(a+1,n-1);)
      _(fold pstr(a;n+1))
      }
}

void pstr_str(char *s1, int n, int m)
  _(requires pstr(s1;n) && str(s1+n;m))
  _(requires n :: low && m :: low && n >= 0 && m >= 0)
  _(ensures str(s1;n+m))
  _(lemma)
{
  if (n == 0){
    _(unfold pstr(s1;n))
  }else{
    _(unfold pstr(s1;n))
    _(apply pstr_str(s1+1,n-1,m);)
    _(fold str(s1;n+m))
  }
}


void striter1(char *s)
  _(requires exists int n. str(s; n) && n :: low)
  _(ensures                str(s; n))
{
  char *p = s;
  _(unfold str(p;n))
  _(fold pstr(s;0))
  int k = 0;  /* k needed just to work around bugs in SecC :) */
  while (*p != 0)
    _(invariant pstr(s;k) && k >= 0 && k <= n && k :: low)
    _(invariant exists char y. (p |-> y) && ((y == 0) :: low) && (y != 0 ? str(p+1;n-k-1) : n == k))
    _(invariant p == s + k)
  {
    p++;
    _(unfold str(p;n-k-1))
    _(apply pstr_snoc(s,k);)
    k++;
  }
  _(fold str(p;0))
  _(apply pstr_str(s,k,0);)

}



void striter2(char *s)
  _(requires exists int n. str(s; n) && n :: low)
  _(ensures                str(s; n))
{
  char *p = s;
  _(unfold str(p;n))
  _(fold pstr(s;0))
  while (*p != 0)
    _(invariant exists int k. pstr(s;k) && k >= 0 && k <= n && k :: low)
    _(invariant exists char y. (p |-> y) && ((y == 0) :: low) && (y != 0 ? str(p+1;n-k-1) : n == k))
    _(invariant p == s + k)
  {
    p++;
    _(unfold str(p;n-k-1))
    _(apply pstr_snoc(s,k);)
  }
  _(fold str(p;0))
  _(apply pstr_str(s,n,0);)

}

void striter3(char *s)
  _(requires exists int n. str(s; n) && n :: low)
  _(ensures                str(s; n))
{
  char *p = s;
  _(unfold str(p;n))
  _(fold pstr(s;0))
  int k = 0;  /* k needed just to work around bugs in SecC :) */
  while (*p != 0)
    _(invariant pstr(s;k) && k >= 0 && k <= n && k :: low)
    _(invariant exists char x. (p |-> x) && ((x == 0) :: low) && (x != 0 ? str(p+1;n-k-1) : n == k))
    _(invariant p == s + k)
  {
    p++;
    _(unfold str(p;n-k-1))
    _(apply pstr_snoc(s,k);)
    k++;
  }
  _(fold str(p;0))
  _(apply pstr_str(s,k,0);)

}
/* Issue 12: now resolved */
int issue_twelve(int *p)
  _(requires exists int v. p |-> v && v :: low)
  _(ensures p |-> v)
{
  int v = *p;
  if (v) ;
}

int strlen_insecure(int *a)
	_(requires exists int n. str(a; n))
	_(ensures                str(a; n))
	_(ensures  result == n)

	/* The reason why this should fail is that n is not public,
	 * which leaks into the branching condition of str.
	 */
	_(fails    insecure)
{
	_(unfold str(a; n))
	int res;

	if(*a != 0) {
		res = strlen_insecure(a + 1) + 1;
	} else {
		res = 0;
	}

	_(fold str(a; n))
	return res;
}
