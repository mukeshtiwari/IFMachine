/* Examples collected by
 * Marco Eilers, Peter Müller, and Samuel Hitz: Modular Product Programs, ESOP 2018
 * See http://viper.ethz.ch/modularproducts
 */

#include "secc.h"
 
int *alloc();
	_(ensures exists int v. result |-> v)

void free(int *x);
	_(requires exists int v. x |-> v)

struct patient {
	int *name;
	int *hiv;
};

/* A. Banerjee and D. A. Naumann: Secure Information Flow and Pointer Confinement in a Java-like Language, CSFW 2002 */

struct patient *patient_read();
	_(ensures exists int *_name.
		&result->name |->[low] _name)

int *high_source();
	_(ensures exists int v. result |-> v) /* result is high */

void banerjee_insecure()
	_(fails insecure)
{
	struct patient *lp = patient_read();
	int *name = lp->name;
 
	struct patient *np;
	_(assume exists int *_name.
		&np->name |-> _name)
	_(assume exists int _hiv.
		&np->hiv |-> _hiv)

	np->name = name;
	np->hiv = high_source();
	
	lp->name = np->hiv; /* this assignment is insecure */
	
	_(assert exists int *_name.
		&np->name |-> _name)
	_(assert exists int *_hiv.
		&np->hiv |-> _hiv)
}

/* D. Costanzo and Z. Shao: A Separation Logic for Enforcing Declarative Information Flow Control Policies, POST 2014 */

void print(int x);
	_(requires x :: low)

int data(int i, int n);
	_(requires i < n)
	_(ensures (result == 0) :: low)

void print_data_secure(int n)
	_(requires n :: low)
{
	int i = 0;
	while(i < n)
		_(invariant i :: low)	
	{
		int x = data(i, n);
		if(x == 0)
			print(i);
		i = i + 1;
	}
}

void print_data_insecure(int n)
	_(fails insecure)
	_(requires n :: low)
{
	int i = 0;
	while(i < n)
		_(invariant i :: low)	
	{
		int x = data(i, n);
		if(x == 1)
			print(i);
		i = i + 1;
	}
}

/* Marco Eilers, Peter Müller, and Samuel Hitz: Modular Product Programs, ESOP 2018, Fig 1 */

int is_female(int person);
	_(ensures (person % 2) :: low ==> result :: low)

int people(int i);
	_(ensures result % 2 :: low)

int count_people(int n)
	_(requires n :: low)
	_(ensures  result :: low)
{
	int count = 0;
	
	int i = 0;
	while(i < n)
		_(invariant i :: low)
		_(invariant count :: low)
	{
		int current = people(i);
		int female = is_female(current);
		count += female;
		i = i + 1;
	}
	
	return count;
}

/* Marco Eilers, Peter Müller, and Samuel Hitz: Modular Product Programs, ESOP 2018, Fig 6 */

int password(int i);
int input(int i);

int check_password(int n)
	_(ensures result :: low)
{
	// XXX: currently don't have sequences
	return 0;
}

/* T. Terauchi and A. Aiken: Secure Information Flow as a Safety Problem, SAS 2005, Fig. 1 */

int terauchi1(int h, int y)
	_(requires y :: low)
	_(ensures  result :: low)
{
	int z = 1;
	int x;
	
	_(assume h :: low)  // no branching on secrets
	
	if(h) {
		x = 1;
	} else {
		x = z;
	}
	
	return x + y;
}


/* T. Terauchi and A. Aiken: Secure Information Flow as a Safety Problem, SAS 2005, Fig. 2 */

int hashfunc(int i);

void declassify(int i);
	_(ensures i :: low)

int terauchi2_insecure(int secret, int hash, int input)
	_(fails insecure)
	_(requires input  :: low)
	_(ensures  result :: low)
{
	if(hashfunc(input) == hash) {
		return secret;
	} else {
		return 0;
	}
}

int terauchi2_secure(int secret, int hash, int input)
	_(requires input  :: low)
	_(ensures  result :: low)
{
	int h = hashfunc(input);
	
	declassify(h == hash);
	declassify(h == hash ? secret : 0);

	if(h == hash) {
		return secret;
	} else {
		return 0;
	}
}

/* T. Terauchi and A. Aiken: Secure Information Flow as a Safety Problem, SAS 2005, Fig. 3 */

int terauchi3(int n, int k)
	_(requires n >= 0)
	_(requires n :: low)
	_(requires k :: low)
	_(ensures  result :: low)
{
	int c = n;
	int f1 = 1;
	int f2 = 0;
	
	while(c > 0)
		_(invariant c :: low && f1 :: low && f2 :: low)
	{
        f1 = f1 + f2;
        f2 = f1 - f2;
        c--;
	}
	
	if(f1 > k) {
		return 1;
	} else {
		return 0;
	}
}


