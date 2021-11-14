/* lemma is illegal since it has side effects, which can lead to unsoundness */
void illegal_lemma(int *a, int i)
_(lemma)
_(fails effects)
_(requires exists int v. a |-> v)
_(ensures a |-> i)
{
  if ((*a = i) == i){
  }
}

/* demonstrates unsoundness of lemmas with side effects. Specifically,
 * if the call to illegal_lemm() is omitted, the deduction is clearly
 * unsound. But this is precisely the purpose of _(apply ...): to allow
 * such calls to be omitted by the compiler. */
void use_illegal_lemma(int *a, int i)
  _(requires exists int v. a |-> v)
  _(ensures a |-> i)
  _(fails effects)
{
  _(apply illegal_lemma(a,i);)
}

/* this lemma is OK and indeed we will probably want lemmas to be
 * able to inspect the heap, so demanding absence of all effects
 * is too stringent. Instead, absence of state modification would
 * appear to be the correct restriction.*/
void legal_lemma(int *a, int i)
_(lemma)
     _(requires exists int v. a |-> v && v :: low)
_(ensures a |-> v)
{
  int x = *a;
  if (x){
  }
}


/* Previously, SecC was conservative and considered the write below
 * to deem the lemma illegal, even though it does not introduce
 * unsoundness.
 * This restriction is now relaxed, and x is (temporarily) ghost state.
 */
void illegal_lemma2()
  _(lemma)
  // _(fails effects)
{
  int x = 0;
  x++;
}

/* test for side-effects during lemma application */
void do_nothing(int i)
  _(lemma)
{
}

int pure_lemma(int i)
	_(pure) _(lemma)
	_(ensures result <=> i == 0)
{
	if(i == 0) return 1;
	else return 0;
}

void impure_lemma(int b, int x)
	_(requires b ==> x :: low)
	_(pure) _(lemma)
	_(fails effects)
{
	if(b) {
		_(assert x :: low)
	}
}

void pure_lemma_calls_non_pure()
	_(fails effects)
{
	do_nothing(0);
}

int broken_apply()
  _(ensures result == 1)
  _(fails effects)
{
  int i = 0;
  _(apply do_nothing(i++);)
    return i;
}

void logical_var_lemma(int x)
  _(lemma)
  _(requires x > 0)
{
}

/* allowed to pass logical variables to _apply */
void logical_var_good(){
  _(assert exists int x. x > 0)
  _(apply logical_var_lemma(x);)
}


void logical_var_func(int x)
  _(requires x > 0)
{
}

/* not allowed to use logical variables in code */
void logical_var_bad()
  _(fails effects)
{
  _(assert exists int x. x > 0)
  logical_var_lemma(x);
}


 void logical_var_branch(){
  _(assert exists int x. x > 0)
    _(apply if (x <= 0) { _(assert (1 == 0)) })
}


int inc(int i){ return i++; }

/* this should fail since we are calling a non-lemma function in the apply */
void apply_inc(int i)
  _(fails effects)
{
  _(apply if (i == i) inc(i);)
}