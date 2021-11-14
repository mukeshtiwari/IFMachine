_(predicate ar(int *a, int i, int j)
	i < j ==> exists int x. &a[i] |-> x && ar(a, i+1, j))

_(predicate str(int *a; int n)
	n == 0 ? a |-> 0 : n > 0 && exists int x. a |-> x && x != 0 && str(a + 1; n - 1))

void ar0(int *a, int i)
    _(lemma)
    _(ensures ar(a,i,i))
{
    _(fold ar(a,i,i))
}

void ar1(int *a, int i)
	_(lemma)
	_(requires  exists int x. &a[i] |-> x)
	_(ensures   ar(a, i, i+1))
{
    _(fold ar(a,i+1,i+1))
    _(fold ar(a,i,i+1))
}

void snoc(int *a, int i, int j)
	_(lemma)
    _(requires i <= j && i :: low && j :: low)
    _(requires ar(a, i, j))
    _(requires exists int x. &a[j] |-> x)
    _(ensures  ar(a, i, j+1))
{
    _(unfold ar(a, i, j))
    if(i < j) {
        snoc(a, i+1, j);
        _(fold ar(a, i, j+1))
    } else {
        _(apply ar1(a, i);)
    }
}

void shift(int *a, int i, int j, int n)
	_(lemma)
    _(requires i :: low && j :: low && n :: low)
    _(requires ar(a, i, j))
    _(ensures  ar(a+n,i-n,j-n))
{
    _(unfold ar(a, i, j))
    if(i < j) {
        _(apply shift(a, i+1, j, n);)
    }
    _(fold ar(a+n, i-n, j-n))
}

void split(int *a, int i, int k, int j)
	_(lemma)
	_(requires i :: low && k :: low)
    _(requires 0 <= i && i <= k && k <= j)
	_(requires ar(a, i, j))
	_(ensures  ar(a, i, k))
	_(ensures  ar(a, k, j))
{
	if(i == k) {
		_(fold ar(a, i, k))
	} else {
		_(unfold ar(a, i, j))
        _(apply split(a, i+1, k, j);)
		_(fold ar(a, i, k))
	}
}

void join(int *a, int i, int k, int j)
	_(lemma)
	_(requires i :: low && k :: low)
    _(requires 0 <= i && i <= k && k <= j)
	_(requires ar(a, i, k))
	_(requires ar(a, k, j))
	_(ensures  ar(a, i, j))
{
	if(i == k) {
		_(unfold ar(a, i, k))
	} else {
		_(unfold ar(a, i, k))
        _(apply join(a, i+1, k, j);)
		_(fold ar(a, i, j))
	}
}

void expose(int *a, int i, int k, int j)
	_(lemma)
	_(requires i :: low && k :: low)
    _(requires 0 <= i && i <= k && k < j)
	_(requires ar(a, i, j))
	_(ensures  ar(a, i, k))
	_(ensures  exists int x. &a[k] |-> x)
	_(ensures  ar(a, k+1, j))
{
	if(i == k) {
		_(fold ar(a, i, k))
		_(unfold ar(a, k, j))
	} else {
		_(unfold ar(a, i, j))
        _(apply expose(a, i+1, k, j);)
		_(fold ar(a, i, k))
	}
}

void cover(int *a, int i, int k, int j)
	_(lemma)
	_(requires i :: low && k :: low)
    _(requires 0 <= i && i <= k && k < j)
	_(requires ar(a, i, k))
	_(requires exists int x. &a[k] |-> x)
	_(requires ar(a, k+1, j))
	_(ensures ar(a, i, j))
{
	if(i == k) {
		_(unfold ar(a, i, k))
		_(fold ar(a, k, j))
	} else {
		_(unfold ar(a, i, k))
        _(apply cover(a, i+1, k, j);)
		_(fold ar(a, i, j))
	}
}


// just memory safety
void *memcpy(int *dest, int *src, int n)
    _(requires 0 <= n && n :: low)
    _(maintains ar(dest, 0, n) && ar(src, 0, n))
{
    int i = 0;
    while(i < n)
        _(invariant 0 <= i && i <= n && i :: low)
        _(invariant ar(dest, 0, n) && ar(src, 0, n))
    {
        _(apply expose(src,  0, i, n);)
        _(apply expose(dest, 0, i, n);)
        dest[i] = src[i];
        _(apply cover(src,  0, i, n);)
        _(apply cover(dest, 0, i, n);)
        i++;
    }
}

int strlen(int *a)
	_(requires exists int n. str(a; n) && n :: low())
	_(ensures                str(a; n))
	_(ensures  result == n)
{
	_(unfold str(a; n))
	int res;

	if(*a != 0) {
		res = strlen(a + 1) + 1;
	} else {
		res = 0;
	}

	_(fold str(a; n))
	return res;
}