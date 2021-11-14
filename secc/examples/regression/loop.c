int *alloc();
	_(ensures exists int v. result |-> v)

void free(int *x);
	_(requires exists int v. x |-> v)

void loop1(int *p)
	_(requires exists int v. p |-> 0)
	_(ensures  exists int w. p |-> w && v <= w)
{
	while(1)
		_(invariant exists int w. p |-> w)
	{
	}
}

int loop2(int y)
	// _(fails incorrect)
	_(requires y :: low() && y >= 0)
	_(requires exists int y0. y0 == y)
	_(ensures  result == y0)
{
	int x = 0;

	while(y > 0)
		_(invariant x + y == y0)
		_(invariant y :: low() && y >= 0)
	{
	  x = x + 1;
	  y = y - 1;
	}

	return x;
	// _(assert x == 0)
}

void loop3(int n)
	_(requires n :: low)
{
	int i = 0;
	int *p = alloc();
	int *q = alloc();
	*q = 2;
	while(i < n)
		_(invariant i :: low)
		_(invariant q |-> 2)
		_(invariant exists int v. p |-> v)
	{ *p = *q; i++; }
	*p = 1;
	_(assert q |-> 2)
	free(p);
	free(q);
}

void loop3_incorrect(int n)
	_(requires n :: low)
	_(fails incorrect)
{
	int i = 0;
	int *p = alloc();
	int *q = alloc();
	*q = 2;
	while(i < n)
		_(invariant i :: low)
		_(invariant exists int v. p |-> v)
		_(invariant exists int v. q |-> v)
	{ *p = 0; *q = 3; i++; }
	*p = 1;
	_(assert q |-> 2)
	free(p);
	free(q);
}

void loop4()
	_(fails memory)
{
	int *p; // not allocated
	while(1) *p = 0;
}

void old_loop(int x)
	_(requires 0 <= x)
{
	while(1)
		_(invariant 0 <= x)
		_(invariant old(x) <= x)
	{
		x++;
	}
}

int add(int x, int y)
	_(requires y >= 0)
	_(requires y :: low())
	_(ensures  result == x + y)
{
	int x0 = x;
	int y0 = y;
	while(y > 0)
		_(invariant y >= 0)
		_(invariant y :: low())
		_(invariant x0 + y0 == x + y)
	{
		x++; y--;
	}

	return x;
}

int add_old(int x, int y)
	_(requires y >= 0)
	_(requires y :: low())
	_(ensures  result == x + y)
{
	while(y > 0)
		_(invariant y >= 0)
		_(invariant y :: low())
		_(invariant old(x + y) == x + y)
	{
		x++; y--;
	}

	return x;
}

void add_test(int x, int y)
	_(requires y >= 0)
	_(requires y :: low())
{
	int r = add(x, y);
	_(assert r == x + y)
}