_(lemma
    forall int i, int j.
        0 <= i && i < j ==> 0 <= j)

_(lemma
    forall int i, int j.
        0 <= i && i < j ==> 0 <= j;
    induct i)

_(function
	int length(list<int> xs))

_(function
	list<int> append(list<int> xs, list<int> ys))

_(function
	bool contains(list<int> xs, int x))

_(axioms
	length(nil) == 0;
	forall int y, list<int> ys.
        length(cons(y,ys)) == length(ys) + 1;
	forall list<int> ys.
		append(nil, ys) == ys;
	forall int x, list<int> xs, list<int> ys.
		append(cons(x,xs), ys) == cons(x, append(xs, ys));
    forall int x.
        contains(nil, x) <=> false;
	forall int y, list<int> ys, int x.
        contains(cons(y,ys), x) <=> (x == y) || contains(ys, x))

_(lemma
    forall list<int> xs.
        length(xs) >= 0;
    induct xs)

_(lemma
    forall list<int> xs.
        length(xs) == 0 ==> xs == nil;
    induct xs)

_(lemma
    forall list<int> xs.
        append(xs, nil) == xs;
    induct xs)

_(lemma
    forall list<int> xs, list<int> ys.
        length(append(xs,ys)) == length(xs) + length(ys);
    induct xs)

_(lemma
	forall list<int> xs, list<int> ys, list<int> zs.
		append(append(xs, ys), zs) == append(xs, append(ys, zs));
    induct xs)

_(lemma
    forall int x, list<int> xs, list<int> ys.
        contains(append(xs, ys), x) <=> contains(xs, x) || contains(ys, x);
    induct xs)

_(function
	bool sorted(list<int> xs))

_(axioms
    sorted(nil);
    forall int x.
        sorted(cons(x,nil));
    forall int x, int y, list<int> ys.
        sorted(cons(x, cons(y, ys)))
            <=> x <= y && sorted(cons(y, ys)))