#include "secc.h"

struct list {
	int *head;
	struct list *next;
};

struct record {
	int is_classified;
	int data;
	struct record *next;
};

_(predicate ls(struct list *l; int length)
       (l == null :: low)
	&& (l == null
		? length == 0
		: length >  0 &&
		  exists int v, struct list *n.
		  	   &l->head |-> v
		  	&& &l->next |-> n
		  	&& ls(n; length - 1)))

_(predicate ls_data(struct list *l; list<int> xs)
    (l == null :: low) &&
    (l == null
    	?   xs == nil
    	: exists struct list *n, int x, list<int> ys.
    	    xs == cons(x, ys) &&
    		&l->head |-> x &&
    		&l->next |-> n &&
    		ls_data(n; ys)))

_(function
  int sum(list<int> xs))

_(rewrites
	sum(nil) == 0;
	forall int x, list<int> xs. sum(cons(x,xs)) == x + sum(xs))

int list_sum(struct list *l)
	_(requires exists list<int> xs. ls_data(l; xs))
	_(ensures ls_data(l; xs))
	_(ensures  result == sum(xs))
{
	_(unfold ls_data(l; xs))
	int res = 0;
	if(l != NULL) {
		res = l->head + list_sum(l->next);
	}
	_(fold ls_data(l; xs))
	return res;
}

_(predicate lseg(struct list *h, struct list *t; int length)
	(length :: low && h :: low && t :: low) &&
       (length == 0 ? h == t : length > 0 &&
		  exists int v, struct list *n.
		  	   &h->head |-> v
		  	&& &h->next |-> n
		  	&& lseg(n, t; length - 1)))

void lseg_length(struct list *p, struct list *q)
	_(requires exists int k.
		lseg(p, q; k))
	_(ensures
		lseg(p, q; k) && k >= 0 && k :: low && p :: low && q :: low)
{
	_(unfold lseg(p, q; k))
	_(fold   lseg(p, q; k))
}

/* This function does not make sense.
 * - list segments can be cyclic, so the termination check is wrong
 * - there needs to be a modification of some ->next

void lseg_append(struct list *p, struct list *r, struct list *q)
	_(requires exists int k, int i.
		lseg(p, r; k) && lseg(r, q; i))
	_(ensures
		lseg(p, q; k + i))
{
	_(unfold lseg(p, r; k))
	lseg_length(r, q);
	if(p == r) {
		_(assert k == 0)
	} else {
		lseg_append(p->next, r, q);
		_(fold lseg(p, q; k + i))
	}
}
 */

void lseg_snoc(struct list *p, struct list *n)
	// _(requires attacker :: high)
    _(requires exists struct list *q, int v, int h.
  		q :: low && lseg(p, n; h) && &n->head |-> v && &n->next |-> q)
	_(ensures
		lseg(p, q; h+1))
{
	_(fold lseg(q, q; 0))
	lseg_length(n, q);
	_(fold lseg(n, q; 1))
	_(assume 0)
	lseg_append(p, n);
}

int length(struct list *l)
	// _(requires attacker :: high)
	_(requires exists int n. ls(l; n))
	_(ensures ls(l; n))
	_(ensures result == n && result :: low)
{
	_(unfold ls(l; n))
	int res = 0;

	if(l != NULL) {
		int i = length(l->next);
		res = i + 1;
	} else {
		res = 0;
	}
	
	_(fold ls(l; n))
	return res;
}

void append(struct list *p, struct list *q)
	_(requires p != null)
	_(requires exists int k, int m.
	    lseg(p, null; m) && lseg(q, null; k))
	_(ensures
	    lseg(p, q; m + k))
{
	struct list *r = p;

	_(unfold lseg(p, null; m))
	_(fold   lseg(p, r; 0))

	// cannot establish loop init here,
	// probably bad matching of n ~> q
	
	while(r->next)
		_(invariant exists int m1, int m2, int v, struct list *n.
		       m == m1 + m2 + 1
		  	&& &r->head |-> v
		  	&& &r->next |-> n
			&& lseg(p, r; m1)
			&& lseg(q, null; k)
			&& lseg(n, null; m2))
	{
		struct list *r0 = r;
		r = r->next;
		_(unfold lseg(n, null; m2))
		_(assert lseg(p, r0; m1))
		_(assert exists int v. &r0->head |-> v)
		_(assert &r0->next |-> n)
		lseg_snoc(p, r0);
	_(assume 0)
	}
	_(assume 0)
	r->next = q;
}

_(predicate records(struct record *head, sec label)
       (head == null :: low)
	&& (head == null
		 ==>
		  exists int c, int d, struct list *n.
		  	   &head->is_classified |-> c && c :: low
		  	&& &head->data          |-> d && d :: (c ? label : low)
		  	&& &head->next          |-> n
		  	&& records(n, label)))

void lemma_records_head(struct record *head)
	_(requires exists sec label. records(head, label))
	_(ensures                    records(head, label))
	_(ensures head == null :: low)
{
	_(unfold records(head, label))
	_(fold   records(head, label))
}

void print(int x);
	_(requires x :: low)

void print_records(struct record *head)
	// _(requires ! attacker :: label)
	_(requires exists sec label. records(head, label))
	_(fails memory)
{
	lemma_records_head(head);
	
	// It's viable to prove absence of leaks
	// with a stronger rule than invariant,
	// i.e., one that treats the loop as if it was a recursion,
	// so that we can fold again all the way back
	while(head == NULL)
		_(invariant head == null :: low)
		_(invariant records(head, label))
	{
		_(unfold records(head, label))

		if(!head->is_classified)
			print(head->data);
		head = head->next;

		lemma_records_head(head);
	}
}
