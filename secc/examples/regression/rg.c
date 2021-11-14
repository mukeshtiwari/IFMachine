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


void some_operation(int *x)
    _(shared exists int _x. x |-> _x rely old(_x) >= 10 ==> _x == old(_x) guarantee true)
{
    _(atomic begin)
    atomic_store(x, 10);
    _(atomic end)
}

void another_operation(int *x)
    _(shared exists int _x. x |-> _x rely true guarantee old(_x) >= 10 ==> _x == old(_x))
{
}

void incompatible_rely(int *x)
    _(fails incorrect)
    _(shared exists int _x. x |-> _x rely old(_x) == 10 ==> _x == old(_x) guarantee true)
{
    some_operation(x);
}

void compatible_rely(int *x)
    _(shared exists int _x. x |-> _x rely old(_x) >= 0 ==> _x == old(_x) guarantee true)
{
    some_operation(x);
}

void incompatible_guarantee(int *x)
    _(fails incorrect)
    _(shared exists int _x. x |-> _x rely true guarantee old(_x) >= 0 ==> _x == old(_x))
{
    another_operation(x);
}

void compatible_guarantee(int *x)
    _(shared exists int _x. x |-> _x rely true guarantee old(_x) >= 20 ==> _x == old(_x))
{
    another_operation(x);
}

void small_share(int *x)
    _(shared exists int _x. x |-> _x rely true guarantee true)
{
}

void partial_share(int *x, int *y)
    _(shared exists int _x, int _y. x |-> _x && y |-> _y rely true guarantee true)
{
    small_share(y);
}

void blub(int *x)
    _(shared exists int _x0, int _x1. x |-> _x0 && x + 1 |-> _x1 rely true guarantee true)
{
}

void bla(int *x)
    _(fails memory)
    _(shared exists int _x. x |-> _x rely true guarantee true)
{
    blub(x);
}

void inc(int *c)
  _(shared     exists int _c. c |-> _c && _c :: low
          rely old(_c) >= 10 ==> _c == old(_c)
     guarantee _c >= old(_c))
{
    _(atomic begin)
        int r = atomic_increment(c);
        _(assert r == _c)
    _(atomic end)

    if (r >= 77 && r <= 88) {
        _(atomic begin)
            int rr = atomic_load(c);
            _(assert r + 1 == rr)
            _(assert r + 1 == _c)
        _(atomic end)
    }
}

void something_that_succeeds(int *x, int *y)
    _(shared    exists int _x, int _y. x |-> _x && y |-> _y
           rely _x >= old(_x) && _y == old(_y)
      guarantee _x >= old(_x) && _y == old(_y))
{
    _(atomic begin)
        int obsx1 = atomic_load(x);
    _(atomic end)
    _(atomic begin)
        int obsy1 = atomic_load(y);
    _(atomic end)

    _(atomic begin)
        int obsx2 = atomic_load(x);
    _(atomic end)
    _(atomic begin)
        int obsy2 = atomic_load(y);
    _(atomic end)

    _(assert obsx1 <= obsx2 && obsy1 == obsy2)
}

void too_many_atomic_calls(int *x)
    _(shared exists int _x. x |-> _x rely true guarantee true)
    _(fails effects)
{
    _(atomic begin)
    int x1 = atomic_load(x);
    int x2 = atomic_load(x);
    _(atomic end)
}

void something_that_fails(int *x)
    _(shared    exists int _x. x |-> _x
           rely _x >= old(_x)
      guarantee _x >= old(_x))
    _(fails incorrect)
{
    _(atomic begin)
        int obs1 = atomic_load(x);
    _(atomic end)

    _(atomic begin)
        int obs2 = atomic_load(x);
    _(atomic end)

    _(assert obs1 == obs2)
}

void invalid_memory_access(int *x, int *y)
    _(shared    exists int _x. x |-> _x
           rely _x >= old(_x)
      guarantee _x >= old(_x))
    _(fails effects)
{
    _(atomic begin)
    *y = 44;
    _(atomic end)
}

void invalid_memory_access2(int *x)
    _(shared    exists int _x. x |-> _x
           rely _x >= old(_x)
      guarantee _x >= old(_x))
    _(fails memory)
{
    *x = 44;
}

void invalid_memory_access3(int *x)
    _(shared    exists int _x. x |-> _x
           rely _x >= old(_x)
      guarantee _x >= old(_x))
    _(fails effects)
{
    _(atomic begin)
    int _x = *x;
    _(atomic end)
}

void invalid_rely(int *x)
    _(shared    exists int _x. x |-> _x
           rely _x >= old(_x)
      guarantee _x >= old(_x))
{
}

void function_without_shared_state(int *x)
{
}

void empty_atomic_block()
{
    _(atomic begin)
    _(atomic end)
}
