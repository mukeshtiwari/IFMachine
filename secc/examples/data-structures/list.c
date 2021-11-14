#include "secc.h"

struct list {
	int head;
	struct list *next;
};

_(predicate ls(struct list *l; list<int> xs)
    (l == null :: low) &&
    (l == null
    	?   xs == nil
    	: exists struct list *n, int x, list<int> ys.
    	    xs == cons(x, ys) &&
    		&l->head |-> x &&
    		&l->next |-> n &&
    		ls(n; ys)))

void ls_low(struct list *l)
	_(requires exists list<int> xs. ls(l; xs))
	_(ensures  ls(l; xs))
	_(ensures  l == null :: low)
{
	_(unfold ls(l; xs))
	_(fold ls(l; xs))
}

_(function
	int sum(list<int> xs))

_(rewrites
	sum(nil) == 0;
	forall int x, list<int> xs. sum(cons(x,xs)) == x + sum(xs))

_(function
	list<int> append(list<int> xs, list<int> ys))

_(rewrites
	forall list<int> ys.
		append(nil, ys) == ys;
	forall int x, list<int> xs, list<int> ys.
		append(cons(x,xs), ys) == cons(x, append(xs, ys)))

_(function
	bool contains(list<int> xs, int x))

_(function
	int length(list<int> xs))

_(rewrites
	length(nil) == 0;
	forall int y, list<int> ys. length(cons(y,ys)) == length(ys) + 1)

_(rewrites
	forall int x. contains(nil, x) <=> false;
	forall int y, list<int> ys, int x. contains(cons(y,ys), x) <=> (x == y) || contains(ys, x))

_(function
	list<int> reverse(list<int> xs))
	
_(rewrites
	reverse(nil) == nil;
	forall int x, list<int> xs. reverse(cons(x,xs)) == append(reverse(xs), cons(x, nil)))

// these are lemmas
_(rewrites
	forall list<int> xs, list<int> ys.
		reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));
	forall list<int> xs, list<int> ys, list<int> zs.
		append(append(xs, ys), zs) == append(xs, append(ys, zs)))

void reverse_reverse(list<int> xs)
	_(lemma)
	_(requires xs :: low)
	_(ensures reverse(reverse(xs)) == xs)
{
	if(xs != nil) {
		_(assert exists int x, list<int> ys. xs == cons(x, ys))
		reverse_reverse(ys);
	}
}

int list_sum(struct list *l)
	_(requires exists list<int> xs. ls(l; xs))
	_(ensures ls(l; xs))
	_(ensures  result == sum(xs))
{
	_(unfold ls(l; xs))
	int res = 0;
	if(l != NULL) {
		res = l->head + list_sum(l->next);
	}
	_(fold ls(l; xs))
	return res;
}

int list_contains(struct list *p, int a)
	_(requires exists list<int> xs. ls(p; xs))
	_(requires a :: low && xs :: low)
	_(ensures  ls(p; xs))
	_(ensures result <=> contains(xs, a)) // use <=> not == to coerce result into bool
{
	_(unfold ls(p; xs))
	if(p == NULL) {
		_(fold ls(p; xs))
		return 0;
	} else {
		int r = p->head == a || list_contains(p->next, a);
		_(fold ls(p; xs))
		return r;
	}
}

struct list *list_append(struct list *p, struct list *q)
	_(requires exists list<int> xs. ls(p; xs))
	_(requires exists list<int> ys. ls(q; ys))
	_(ensures  ls(result; append(xs, ys)))
{
	_(unfold ls(p; xs))
	if(p == NULL) {
		return q;
	} else {
		struct list *r = list_append(p->next, q);
		p->next = r;
		_(fold ls(p; append(xs, ys)))
		return p;
	}
}

struct list *list_reverse(struct list *head)
	_(requires exists list<int> xs. ls(head; xs))
	_(requires xs :: low)
	_(ensures  ls(result; reverse(xs)))
{
	struct list *curr = head;
	struct list *next = NULL;
	struct list *prev = NULL;
	
	ls_low(curr);
	_(assert xs == append(reverse(nil), xs))
	_(fold   ls(prev; nil))
	while(curr != NULL)
		_(invariant curr == null :: low)
		_(invariant exists list<int> ys, list<int> zs.
		    ys :: low && zs :: low &&
			xs == append(reverse(ys), zs))
		_(invariant
			ls(prev; ys) && ls(curr; zs))
	{
		_(unfold ls(curr; zs))
		next = curr->next;
		curr->next = prev;
		prev = curr;
		curr = next;
		ls_low(curr);
		_(assert exists int z. &prev->head |-> z)
		_(fold ls(prev; cons(z, ys)))
	}

	_(unfold ls(curr; zs))
	_(apply reverse_reverse(ys);)
	return prev;
}
