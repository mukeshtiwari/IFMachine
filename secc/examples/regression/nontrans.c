
/* show how to encode non-transitive policies: for each pincipal X we
 * have two security levels: 
 *   X_input -- the label used to label input generated by X 
 *   X_space -- the label used to label the "workspace" or memory of X
 *
 * We want to be able to define who is allowed to see the data of each
 * principal.  This it the data /generated/ by each principal, X,
 * i.e. the X_input labelled data.  Which principals, Y, are allowed
 * to see it is then governed by which Y_space labels that the policy
 * allows X_input data to flow to, i.e. Y can learn X's data when
 * X_input <= Y_space in the security lattice.
 *
 * Even though the lattice itself is transitive, we can still encode
 * non-transitive policies as the following example demonstrates.
 * Here Alice wants to share her data with Bob but doesn't want Carol
 * to see it.  Bob is happy to share with them both.  Carol is happy
 * to share her data with Bob but not Alice.  
 */
_(constant sec alice_input)
_(constant sec bob_input)
_(constant sec carol_input)
_(constant sec alice_space)
_(constant sec bob_space)
_(constant sec carol_space)

_(axioms
  alice_input <= bob_space;
  bob_input   <= alice_space;
  bob_input   <= carol_space;
  carol_input <= bob_space)


void test(int * alice, int * bob, int * carol, int ai, int bi, int ci)
  _(requires ai :: alice_input)
  _(requires bi :: bob_input)  
  _(requires ci :: carol_input)  
  _(requires exists int _a. alice |->[alice_space] _a)
  _(requires exists int _b.   bob |->[bob_space] _b)
  _(requires exists int _c. carol |->[carol_space] _c)
  _(ensures alice |->[alice_space] bi)
  _(ensures bob |->[bob_space] ai + ci)
  _(ensures carol |->[carol_space] bi)
{
  *alice = bi;
  *bob = ai + ci;
  *carol = bi;
}

void test2(int * alice, int * bob, int * carol, int ai, int bi, int ci)
  _(fails insecure)
  _(requires ai :: alice_input)
  _(requires bi :: bob_input)  
  _(requires ci :: carol_input)  
  _(requires exists int _a. alice |->[alice_space] _a)
  _(requires exists int _b.   bob |->[bob_space] _b)
  _(requires exists int _c. carol |->[carol_space] _c)
  _(ensures alice |->[alice_space] bi)
  _(ensures bob |->[bob_space] ai + ci)
  _(ensures carol |->[carol_space] bi)
{
  *alice = bi;
  *bob = ai + ci;
  *carol = bi + ai;
}
