// run with -no:mod

_(axioms
    forall int a, int b.
        0 <= a && 0 < b && a < b ==> a%b == a;
	forall int a, int b.
		0 <= a && 0 < b ==> (a + b)%b == a%b)

_(predicate ar(int *a; int n)
    0 < n ==> exists int x.
        a |-> x && ar(a+1; n-1))

/* Slice a[i%n]...a[j%n] of array a[0]...a[n] */
_(predicate slice(int *a, int i, int j; int n, sec l)
	i < j ==> exists int x.
		&a[i%n] |-> x && x :: l && slice(a, i+1, j; n, l))

void slice_0(int *a, int i, int n, sec l)
    _(lemma)
    _(ensures slice(a, i, i; n, l))
{
    _(fold slice(a, i, i; n, l))
}

void slice_1(int *a, int i, int n, sec l)
    _(lemma)
    _(requires exists int x. &a[i%n] |-> x && x :: l)
    _(ensures slice(a, i, i+1; n, l))
{
    slice_0(a, i+1, n, l);
	_(fold slice(a, i, i+1; n, l))
}

void slice_snoc(int *a, int i, int j, int n, sec l)
    _(lemma)
    _(requires i <= j && i :: low && j :: low)
    _(requires slice(a, i, j; n, l))
    _(requires exists int x. &a[j%n] |-> x && x :: l)
    _(ensures  slice(a, i, j+1; n, l))
{
    _(unfold slice(a, i, j; n, l))
    if(i < j) {
        slice_snoc(a, i+1, j, n, l);
        _(fold slice(a, i, j+1; n, l))
    } else {
        slice_1(a, j, n, l);
    }
}

void slice_concat(int *a, int i, int k, int j, int n, sec l)
    _(lemma)
    _(requires i <= k && k <= j)
    _(requires i :: low && k :: low && j :: low)
    _(requires slice(a, i, k; n, l))
    _(requires slice(a, k, j; n, l))
    _(ensures  slice(a, i, j; n, l))
{
    _(unfold slice(a, i, k; n, l))
    if(i < k) {
        slice_concat(a, i+1, k, j, n, l);
        _(fold slice(a, i, j; n, l))
    }
}

void slice_high(int *a, int i, int j, int n, sec l)
    _(lemma)
    _(requires i :: low && j :: low)
    _(requires slice(a, i, j; n, l))
    _(ensures  slice(a, i, j; n, high))
{ 
    _(unfold slice(a, i, j; n, l))
    if(i < j) slice_high(a, i+1, j, n, l);
    _(fold slice(a, i, j; n, high))
}

void slice_rotate(int *a, int i, int j, int n, sec l)
    _(lemma)
    _(requires i :: low && j :: low && n :: low && 0 <= i && i <= j && 0 < n)
    _(requires slice(a, i, i+n; n, l))
    _(ensures  slice(a, j, j+n; n, l))
{
   if(i < j) {
       _(unfold slice(a, i, i+n; n, l))
       _(assert (i+n)%n == i%n)
       slice_snoc(a, i+1, i+n, n, l);
       slice_rotate(a, i+1, j, n, l);
   }
}

void slice_from_ar(int *a, int i, int k, int n)
    _(lemma)
    _(requires ar(a + i; k))
    _(requires k :: low && 0 <= i && 0 <= k && i + k <= n)
    _(ensures  slice(a, i, i + k; n, high))
{
    _(unfold ar(a + i; k))
    if(k != 0) {
        _(assert 0 <= i && 0 < n && i < n) // triggers the rewrite rule
        _(assert i%n == i)
        slice_from_ar(a, i+1, k-1, n);
    }
    _(fold slice(a, i, i + k; n, high))
}

struct rb_t {
    int *data;
    int capacity;
    int write_index;
    int read_index;
    _(int write_index1;)
    _(int read_index1;)
};

_(predicate rb_shared(struct rb_t *buf; int *_data, int _capacity, int _write_index, int _read_index, int _write_index1, int _read_index1, sec _level)
    exists int *__data, int __capacity.
    __data == _data && __capacity == _capacity &&
    &buf->write_index |-> _write_index &&
    &buf->read_index  |-> _read_index &&
    &buf->write_index1 |-> _write_index1 &&
    &buf->read_index1  |-> _read_index1 &&
    _write_index :: low && _read_index :: low && _read_index1 :: low && _write_index1 :: low &&
    0 <= _read_index && _read_index <= _read_index1 && _read_index1 <= _read_index + 1 &&
    _read_index1 <= _write_index && _write_index <= _write_index1 && _write_index1 <= _write_index + 1 &&
    _write_index1 <= _read_index + _capacity &&
    0 < _capacity &&
    slice(_data, _read_index1, _write_index; _capacity, _level) &&
    slice(_data, _write_index1, _read_index + _capacity; _capacity, _level))

_(predicate rb_non_shared(struct rb_t *buf; int *_data, int _capacity)
    &buf->data        |-> _data &&
    &buf->capacity    |-> _capacity &&
    _capacity :: low)

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

void rb_put(struct rb_t * buf, int byte)
    _(shared     exists int * d, int c, int wi, int wi1, int ri, int ri1. rb_shared(buf; d, c, wi, ri, wi1, ri1, low)
       rely      wi == old(wi) && wi1 == old(wi1) && c == old(c) && d == old(d) && ri1 >= old(ri1) && ri >= old(ri)
       guarantee ri == old(ri) && ri1 == old(ri1) && c == old(c) && d == old(d) && wi1 >= old(wi1) && wi >= old(wi))
    _(requires exists int *d2, int c2. rb_non_shared(buf; d2, c2) && d2 == d && c2 == c)
    // TODO: We need fractional permissions to distribute rb_non_shared (the read-only parts of rb_shared) to multiple threads
    _(ensures  rb_non_shared(buf; d2, c2) && d2 == d && c2 == c)
    _(maintains wi1 == wi)
    _(requires byte :: low)
{
    _(atomic begin)
        _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
        int _wi = atomic_load(&buf->write_index);
        _(fold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
    _(atomic end)

    _(atomic begin)
        _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
        int _ri = atomic_load(&buf->read_index);
        _(fold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
    _(atomic end)

    _(unfold rb_non_shared(buf; d2, c2))
    if (_wi >= _ri + buf->capacity) {
        _(fold rb_non_shared(buf; d2, c2))
        rb_put(buf, byte);
    } else {
        _(atomic begin)
            _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
            _(unfold slice(d, wi, ri+c; c, low))
            _(apply buf->write_index1 += 1;)
            _(fold rb_shared(buf; d, c, wi, ri, wi1+1, ri1, low))
        _(atomic end)

        int index = _wi % buf->capacity;
        _(assert exists int a. d2+index |-> a)
        buf->data[index] = byte;

        _(atomic begin)
            _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
            atomic_increment(&buf->write_index);
            _(apply slice_snoc(d, ri1, wi, c, low);)
            _(fold rb_shared(buf; d, c, wi+1, ri, wi1, ri1, low))
        _(atomic end)

        _(fold rb_non_shared(buf; d2, c2))
    }
}

int rb_get(struct rb_t * buf)
    _(shared     exists int * d, int c, int wi, int wi1, int ri, int ri1. rb_shared(buf; d, c, wi, ri, wi1, ri1, low)
       rely      ri == old(ri) && ri1 == old(ri1) && c == old(c) && d == old(d) && wi1 >= old(wi1) && wi >= old(wi)
       guarantee wi == old(wi) && wi1 == old(wi1) && c == old(c) && d == old(d) && ri1 >= old(ri1) && ri >= old(ri))
    _(requires exists int *d2, int c2. rb_non_shared(buf; d2, c2) && d2 == d && c2 == c)
    _(ensures  rb_non_shared(buf; d2, c2) && d2 == d && c2 == c)
    _(maintains ri1 == ri)
{
    _(atomic begin)
        _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
        int _ri = atomic_load(&buf->read_index);
        _(fold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
    _(atomic end)

    _(atomic begin)
        _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
        int _wi = atomic_load(&buf->write_index);
        _(fold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
    _(atomic end)

    if (_ri >= _wi) {
        return rb_get(buf);
    } else {
        _(unfold rb_non_shared(buf; d2, c2))

        _(atomic begin)
            _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
            _(unfold slice(d, ri, wi; c, low))
            _(apply buf->read_index1 += 1;)
            _(fold rb_shared(buf; d, c, wi, ri, wi1, ri1+1, low))
        _(atomic end)

        int index = _ri % buf->capacity;
        _(assert exists int a. &(d2[index]) |-> a)
        int result = buf->data[index];

        _(atomic begin)
            _(unfold rb_shared(buf; d, c, wi, ri, wi1, ri1, low))
            atomic_increment(&buf->read_index);
            _(assert 0 <= ri && 0 < c)
            _(assert (ri + c)%c == ri%c)
            _(apply slice_snoc(d, wi1, ri+c, c, low);)
            _(fold rb_shared(buf; d, c, wi, ri+1, wi1, ri1, low))
        _(atomic end)

        _(fold rb_non_shared(buf; d2, c2))
        return result;
    }
}
