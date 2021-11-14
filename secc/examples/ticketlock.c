int atomic_store(int *l, int v1);
    _(atomic)
    _(requires exists int v0. l |-> v0)
    _(ensures  l |-> v1)

int atomic_load(int *l);
    _(atomic)
    _(requires  exists int v0. l |-> v0)
    _(ensures   l |-> v0)
    _(ensures   result == v0)

int atomic_compare_exchange(int *l, int v1, int v2);
    _(atomic)
    _(requires exists int v0. l |-> v0)
    _(ensures  result == v0)
    _(ensures  l |-> (v0 == v1 ? v2 : v0))

int atomic_increment(int *l);
    _(atomic)
    _(requires exists int v0. l |-> v0)
    _(ensures  result == v0)
    _(ensures  l |-> v0 + 1)

struct lock {
	int curr;
	int next;
	_(list<int> queue;)
};

_(function int length(list<int> xs))
_(function bool contains(int x, list<int> xs))
_(function list<int> snoc(list<int> xs, int z))
_(function list<int> append(list<int> xs, list<int> ys))

_(axioms
		length(nil) == 0;
	forall int x.
		contains(x, nil) <=> false;
	forall int x, int y, list<int> ys.
		contains(x, cons(y,ys)) <=> x == y || contains(x, ys);
	forall int y, list<int> ys.
		length(cons(y,ys)) == length(ys) + 1;
	forall list<int> xs, int z.
		snoc(xs, z) == append(xs, cons(z, nil));
	forall list<int> ys.
		append(nil, ys) == ys;
	forall int x, list<int> xs, list<int> ys.
		append(cons(x,xs), ys) == cons(x, append(xs, ys)))

void list_lemmas(list<int> xs)
	_(pure) _(lemma)
	_(ensures length(xs) >= 0)
	_(ensures forall int z.
		snoc(xs, z) != xs)
	_(ensures forall int z.
		length(snoc(xs, z)) == length(xs) + 1)
	_(ensures forall list<int> ys.
		length(append(xs, ys)) == length(xs) + length(ys))
	_(ensures forall int x, list<int> ys.
		contains(x, append(xs, ys)) <=> contains(x, xs) || contains(x, ys))
{
	if(xs != nil) {
		_(assert exists int x, list<int> zs.
			xs == cons(x,zs))
		list_lemmas(zs);
	}
}

void snoc_length(list<int> xs, int y)
	_(pure) _(lemma)
	_(ensures length(xs) >= 0)
	_(ensures snoc(xs, y) != xs)
	_(ensures length(snoc(xs, y)) == length(xs) + 1)
{
	list_lemmas(xs);
}

_(predicate inv(int *p)
    exists int _p. p |-> _p)

_(predicate ticketlock(struct lock *l; int *p, int c, int n, list<int> q)
	 &l->curr  |-> c && c :: low &&
	 &l->next  |-> n && n :: low &&
	 &l->queue |-> q && q :: low &&
	 0 <= c && c + length(q) == n &&
	 (c == n ==> inv(p)))

void ticketlock_init(struct lock *l, int *p)
	_(requires exists int c, int n, list<int> q.
		 &l->curr |-> c && &l->next |-> n && &l->queue |-> q)
	_(requires inv(p))
	_(ensures  ticketlock(l; p, 0, 0, nil))
{
     l->curr = 0;
     l->next = 0;
     _(l->queue = nil;)
     _(fold ticketlock(l; p, 0, 0, nil))
}

void ticketlock_acquire(struct lock *l, int *p)
	_(shared exists int c, int n, list<int> q.
		ticketlock(l; p, c, n, q)
		rely      old(c) <= c && old(n) <= n && (contains(TID, q) <=> contains(TID, old(q)))
		guarantee true
		)
	_(ensures inv(p))
{
	_(atomic begin)
	_(unfold ticketlock(l; p, c, n, q))
	int ticket = atomic_increment(&l->next);
	_(apply snoc_length(q, TID);)
	_(l->queue = snoc(q, TID);)
	_(fold ticketlock(l; p, c, n+1, snoc(q, TID)))
	_(atomic end)

	while(1)
		_(invariant ticket :: low)
	{
		_(atomic begin)
		_(unfold ticketlock(l; p, c, n, q))
		int snapshot = atomic_load(&l->curr);
		_(assert c == snapshot)
		_(assume c <= ticket && ticket <= n)
		_(if(snapshot == ticket) {
			_(assert inv(p))
		})
			_(assume false)
		_(atomic end)

		if(snapshot == ticket) {
			return;
		}
	}
}

/*
void ticketlock_release(int *now_serving)
	_(shared exists int s.
		 now_serving |-> s && s :: low
		 rely true
		 guarantee true)
{
	_(atomic begin)
	atomic_increment(now_serving);
	_(atomic end)
} */
