
_(function bool r(int x0, int x1) = x0 <= x1)
_(function bool g(int x0, int x1) = x0 <= x1)

int atomic_load(int *l);
    _(atomic)
    _(requires  exists int v0. l |-> v0)
    _(ensures   l |-> v0)
    _(ensures   result == v0)

int test(int *x)
  _(shared exists int _x. x |-> _x
    rely r(old(_x), _x)
    guarantee g(old(_x), _x))
  _(ensures result == _x)
{
  _(atomic begin)
  int x0 = atomic_load(x);
  _(atomic end)

  return x0;
}
