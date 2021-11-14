#define _(...)

enum {
	UNLOCKED,
	LOCKED
};

struct lock
{
    int is_locked;
    _(int owner;)
};

_(predicate inv(int *p)
    exists int _p. p |-> _p)

_(predicate mylock(struct lock *l; int *p, int _o, int _l)
    _l :: low && &l->is_locked |-> _l && &l->owner |-> _o && (_l == 1 || _l == 0)
        && (_l == UNLOCKED ==> inv(p) && _o == 0))

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
    _(requires exists int v0. l |-> v0 && v0 :: low)
    _(ensures  result == v0)
    _(ensures  l |-> v0 + 1)


void acquire_lock(struct lock *l, int *p)
    _(shared    exists int o, int x. mylock(l; p, o, x)
           rely old(o) == TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o)
      guarantee old(o) != TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o))
    _(ensures inv(p) && o == TID && x == LOCKED)
{
    _(atomic begin)
        _(unfold mylock(l; p, o, x))

        int r = atomic_compare_exchange(&l->is_locked,UNLOCKED,LOCKED);
        _(apply if (r == UNLOCKED) { l->owner = TID; })

        _(fold mylock(l; p, r == UNLOCKED ? TID : o, LOCKED))
    _(atomic end)

    if (r != UNLOCKED) {
        acquire_lock(l, p);
    }
}

void release_lock(struct lock *l, int *p)
    _(shared    exists int o, int x. mylock(l; p, o, x)
           rely old(o) == TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o)
      guarantee old(o) != TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o))
    _(requires inv(p) && o == TID && x == LOCKED)
{
    _(atomic begin)
        _(unfold mylock(l; p, o, x))

        atomic_store(&l->is_locked,UNLOCKED);
        _(apply l->owner = 0;)

        _(fold mylock(l; p, 0, UNLOCKED))
    _(atomic end)
}

void do_something_with_lock(struct lock *l, int *p)
    _(shared    exists int o, int x. mylock(l; p, o, x)
           rely old(o) == TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o)
      guarantee old(o) != TID ==> old(x) == LOCKED ==> x == old(x) && o == old(o))
{
    acquire_lock(l,p);
    _(unfold inv(p))
    *p = 43;
    _(fold inv(p))
    release_lock(l,p);
}