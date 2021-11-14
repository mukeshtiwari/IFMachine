// SecC: https://bitbucket.org/covern/secc/

/*
[x]    1.  Prove that this algorithm converts an input list into a tree.
[x]    2.  Prove that the algorithm is memory-safe.
[x]    3.  Prove that if the input list is sorted then the resulting tree is a BST.
[x]    4.  Prove that the resulting BST is balanced.
[o]    5.  Prove that the algorithm terminates.
[ ]    6.  (Optional) Prove the above for an iterative version ofsize.
*/

struct list {
	int data;
    struct list *prev;
	struct list *next;
};

_(function
	int length(list<int> xs))

_(function
	bool contains(list<int> xs, int x))

_(function
	bool sorted(list<int> xs))

_(function
	list<int> append(list<int> xs, list<int> ys))

// definitions
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

// some obvious lemmas (not proved here)
_(axioms
    forall list<int> xs.
        length(xs) >= 0;
    forall list<int> xs.
        length(xs) == 0 ==> xs == nil;
    forall list<int> xs.
        append(xs, nil) == xs;
    forall list<int> xs, list<int> ys.
        length(append(xs,ys)) == length(xs) + length(ys);
	forall list<int> xs, list<int> ys, list<int> zs.
		append(append(xs, ys), zs) == append(xs, append(ys, zs));
    forall int x, list<int> xs, list<int> ys.
        contains(append(xs, ys), x) <=> contains(xs, x) || contains(ys, x))

// predicate that characterizes essentially a singly linked list
// no constraints on the prev pointers (irrelevant for this challenge)
// but we track permissions of these fields
_(predicate dll(struct list *l;
                list<int> xs)
    (l :: low) &&
    (!l
    	? xs == nil
    	: exists struct list *n, struct list *p, int y, list<int> ys.
    	    xs == cons(y, ys) &&
    		&l->data |-> y &&
    		&l->prev |-> p &&
    		&l->next |-> n &&
    		dll(n; ys)))


// predicate that characterizes a linked tree
// the list xs collects the elements in the tree inorder
// and the constraint on the list lengths essentially captures balance
_(predicate tr(struct list *n; list<int> xs)
    (n == null :: low) &&
    (n == null
    	?   xs == nil
    	: exists struct list *l, struct list*r,
                 int y, list<int> ys, list<int> zs.
    	    xs == append(ys, cons(y, zs)) &&
            (length(ys) == length(zs) ||
             length(ys) == length(zs) + 1) &&
    		&n->data |-> y &&
    		&n->prev |-> l &&
    		&n->next |-> r &&
    		tr(l; ys) && tr(r; zs)))

// compute the size (recursively)
// to coincide with the length of the list
int size(struct list *l)
    _(requires exists list<int> xs.
                dll(l; xs))
    _(ensures   dll(l; xs))
    _(ensures   result == length(xs) && result :: low)
{
    _(unfold dll(l; xs))
    if(l) {
        // termination measure (not done in the competition)
        _(assert exists struct list *n, list<int> ys.
            &l->next |-> n && dll(n; ys))
        _(assert length(ys) < length(xs))

        int r = size(l->next);
        _(fold dll(l; xs))
        return r + 1;
    } else {
        _(fold dll(l; xs))
        return 0;
    }
}

// dummy type to return pairs of pointers
// SecC does not support the idiom to return these via pointers,
// because taking addresses of static/local variables is not implemented
struct pair {
    struct list *root;
    struct list *right;
};

struct list *dll_to_bst(struct list *head)
    _(requires exists list<int> xs.
                xs :: low && dll(head; xs))
    _(ensures tr(result; xs))
{
    struct list *root;
    struct list *right;
    int n = size(head);
    struct pair r;

    r = dll_to_bst_rec(head, n);
    // struct constants currently not unsupported in the code,
    // so we simply assume the effect of the respective assigments
    _(assume r.root == root && r.right == right)

    // give an explicit name to the list yr...
    _(assert exists list<int> yr.
                dll(right; yr))
    // ...such that we can refer to it and prompt the solver to find this
    // via the size constraints of the postcondition of dll_to_bst_rec
    _(assert yr == nil)

    // finally get rid of the empty heap chunk of the list
    // (right must be NULL, as yr is null)
    _(unfold dll(right; yr))
    return root;
}

struct pair dll_to_bst_rec(struct list *head, int n)
    // note: n >= 0 required for some arithmetic reasoning below
    _(requires n :: low && n >= 0)

    // this gives us a list of length at least n
    _(requires exists list<int> xs.
                xs :: low && dll(head; xs) && length(xs) >= n)

    // this gives us the corresponding split
    // (could be proved by a lemma, though)
    _(ensures  exists list<int> ys, list<int> yr.
                ys :: low && yr :: low && xs == append(ys, yr) && length(ys) == n)
    _(ensures   tr(result.root; ys))
    _(ensures   dll(result.right; yr))
{
    if(n > 0) {
        struct pair r;
        struct pair s;
        
        // first recursive call
        // ensure termination (otherwise unchecked by SecC)
        _(assert n/2 < n)
        r = dll_to_bst_rec(head, n/2);
        struct list *left;
        struct list *root;
        _(assume r.root == left && r.right == root)

        // give names to the sublists ys, yr
        _(assert exists list<int> ys.
            tr(left; ys))
        _(assert exists list<int> yr.
            dll(root; yr))

        _(unfold dll(root; yr))
        // this follows from the fact that n-n/2 > 0
        _(assert yr != nil)
        // and hence we have the following decomposition
        _(assert exists int z, list<int> zs, struct list *m, struct list *q.
            yr == cons(z, zs) &&
    		&root->data |-> z &&
    		&root->prev |-> q &&
    		&root->next |-> m &&
    		dll(m; zs))

        // second recursive call
        // ensure termination (otherwise unchecked by SecC)
        int m = n-n/2-1;
        _(assert m == n/2 || m + 1 == n/2)
        _(assert m < n)
        r = dll_to_bst_rec(root->next, m);
        struct list *temp;
        struct list *right;
        _(assume r.root == temp && r.right == right)

        // the names zs1 and zs2 are bound so that we can fold the predicate below
        _(assert exists list<int> zs1, list<int> zs2.
            zs == append(zs1, zs2) &&
            tr(left; ys) && tr(temp; zs1) && dll(right; zs2))

        root->prev = left;
        root->next = temp;

        _(fold tr(root; append(ys, cons(z, zs1))))

        // fix the result (again, no support for struct assignmens)
        _(assume s.root == root && s.right == right)
        return s;
    } else {
        struct pair r;
        // fix the result (again, no support for struct assignmens)
        _(assume r.root  == null)
        _(assume r.right == head)

        // fold the empty tree
        _(fold tr(r.root; nil))
        return r;
    }
}

// properties of sorted lists
_(axioms
    forall int y, list<int> ys, int y, list<int> zs.
        sorted(append(ys, cons(y, zs))) 
            ==>    sorted(ys)
                && sorted(zs)
                && (forall int x. contains(ys, x) ==> x <= y)
                && (forall int x. contains(zs, x) ==> x >= y))

// witness the BST property by implementing a lookup algorithm:
// this algorithm works only if n is a BST
// moreover, demonstrate logarithmic complexity as the size decreases by half
bool lookup(int x, struct list *n)
    _(requires exists list<int> xs.
                tr(n; xs))
    _(requires x :: low && xs :: low)
    _(requires  sorted(xs))
    _(ensures   tr(n; xs))
    _(ensures result <=> contains(xs, x))
{
    bool found;

    _(unfold tr(n; xs))

    if(n) {
        _(assert exists struct list *l, struct list *r,
                 int y, list<int> ys, list<int> zs.
    	    xs == append(ys, cons(y, zs)) &&
    		&n->data |-> y &&
    		&n->prev |-> l &&
    		&n->next |-> r &&
    		tr(l; ys) && tr(r; zs))
        
        // don't bother with security here
        // (would need to know that append is injective)
        _(assume y :: low && ys :: low && zs :: low)

        if(x < n->data) {
            // follows from sorting, Z3 hangs, see BST.thy using Isabelle's strong definition of sorted
            _(assert contains(xs, x) ==> contains(ys, x))

            // termination: ys is strictly smaller than xs
            _(assert length(ys) < length(xs))

            // logarithmic complexity: length is at most half
            _(assert length(ys) <= length(xs) / 2)
            found = lookup(x, n->prev);
        } else if(x > n->data) {
            // follows from sorting, Z3 hangs, see BST.thy
            _(assert contains(xs, x) ==> contains(zs, x))

            // termination: zs is strictly smaller than xs
            _(assert length(zs) < length(xs))

            // logarithmic complexity: length is at most half
            _(assert length(zs) <= length(xs) / 2)
            found = lookup(x, n->next);
        } else {
            found = 1;
        }
    } else {
        found = 0;
    }

    _(fold tr(n; xs))
    return found;
}