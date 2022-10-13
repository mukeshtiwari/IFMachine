#include "secc.h"

#define NULL 0

#if __SECC
typedef int double;
#endif

/* 
This linked list stores the private data of a client, e.g., a hospital. 
This data will be used locally by the hospital to refine a model, received 
from a federated server. In our case, we are using differentially private 
linear regress, using Gradient Descent, which is modified version of ANoise−GD
to compute theta1 and theta2, rather than p25 and p75. Moroever, the ANoise−GD
is a adapted version of stochastic gradient descent algorithm. In ANoise−GD,
we take all the data points in the training set, while in stochastic gradient
descent, we take a subset of the data points in the training set. 

The differenc
is that in ANoise−GD, we use the data points in the training set to compute
the gradient, while in stochastic gradient descent, we use a subset of the
data points to compute the gradient.

https://arxiv.org/pdf/1405.7085.pdf 
https://arxiv.org/pdf/1607.00133.pdf
*/
struct private_training_data
{
  double x;
  double y;
  struct private_training_data *next;
};


/*
This enum represents an event. Received represents the parameter received 
from the federated server, Training represents the client refining the 
model locally on its private data points (training on a give data with 
the parametersreceived in the Received phase),  Conveyed represents the 
final parameters update to the server. Refilled replenishes the budget 
periodically after certain amount of time, set by client. 
*/
enum ev_status
{
  Received, 
  Training,
  Conveyed,
  Refilled
};
typedef enum ev_status event_status;

// This enum represents if a function failed or succeed, used in the 
// case if there is not enough budget to run the function.
enum ret_code 
{
  Failure, /* if a client is out of budget, it will simply return 
   the received model parameters to server */ 
  Success // if a client has enough budget, it will train 
};
typedef enum ret_code status_code;


/* 
The event is logged in a file for auditing purposes, in case 
of dispute between the server and client by trusted third party. 
Question: Can we trun this into a Zero-Knoweldge-Proof (zk-SNARK)
where the client can prove that the server it is following the 
protocol without revealing any information? I remember Toby tweeted 
a paper where there was some sort of proof about the learning (find 
the paper and understand it).
*/
struct event
{
  event_status est;
  double m; 
  double c; 
  // When est == Training
  double m_old; // old m 
  double c_old; // old c 
  double dm; // averaged m 
  double dc; // averaged c
  double noise1; // noise added to m_new = m_old - learning_rate * (dm + noise1)
  double noise2; // noise added to c_new = c_old - learning_rate * (dc + noise2)
};


/* 
Input-Output history modelled as list, and this list contains enough 
information (snap shot of variousvariables during the program execution)
to ensure the declassification. 
*/
_(predicate io_trace(;list<struct event> xs))

/*
This predicate encodes the valid memory spots for the training data xs and
n is length of xs.
*/
_(predicate valid_memory_inv(;struct private_training_data *xs, int n)
   (xs == null :: low) &&
   (xs == null ? n == 0 : 
       (exists double u, double v, struct private_training_data *xss.
        &xs->x |-> u && (u :: high) && &xs->y |-> v && (v :: high) &&
        &xs->next |-> xss && (0 <= (n - 1)) && valid_memory_inv(;xss, n-1))))


/*
This linked list stores the yhat, predicated from the continiously refining 
theta1 and theta2. yhat = theta1 * x + theta2, which subsequently used to
compute the error (loss function).  
*/
struct yvector
{
  double head;
  struct yvector *next;
};

/*
This predicate encodes the valid memory spots for the yvector ys and
n is length of ys.
*/
_(predicate valid_yvector_inv(;struct yvector *ys, int n)
    (ys == null :: low) &&
    (ys == null ? n == 0 : 
        (exists double u, struct yvector *yss.
        &ys->head |-> u && (u :: high) && &ys->next |-> yss && 
        (0 <= (n - 1)) && valid_yvector_inv(;yss, n-1))))



/*
This logical function computes the budget from a trace of events.
During the training, it is used to ensure (prove) that the client
has enough budget to run the training. Every training event 
consumes a eps amount of budget, while the refill event replenishes
the budget by refvalue amount.
*/
_(function double count_total_budget(double eps, double refvalue, list<struct event> iost))
_(rewrites
    forall double eps, double refvalue. count_total_budget(eps, refvalue, nil) == 0;
    forall double eps, double refvalue, struct event e, list<struct event> es. 
      count_total_budget(eps, refvalue, cons(e, es)) == 
      ((e.est == Training) ? (-eps + count_total_budget(eps, refvalue, es)) :
       ((e.est == Refilled) ? (refvalue + count_total_budget(eps, refvalue, es)) :
         count_total_budget(eps, refvalue, es))))  


/*
This logical function appends two lists, xs and ys, and returns the
resulting list.
*/
_(function list<struct event> append(list<struct event> xs, list<struct event> ys))
_(rewrites
	forall list<struct event> ys. append(nil, ys) == ys;
	forall struct event x, list<struct event> xs, list<struct event> ys.
		append(cons(x, xs), ys) == cons(x, append(xs, ys)))

/*
Trace is: 
(Round 1 epoch) Refilled, Received, Training, Training, Training, Training, 
Conveyed, Refilled, (round 2 epoch:) 
Refilled, Received, Training, Training,  Training,  Training, Conveyed, Refilled

Notice here that once the training thread acquires the lock, it will continue 
to train until it finishes. The the replenish thread will get the lock 
replenish the budget.
*/

/*
This predicate encodes when a point is safe to release to the federated server. Imagine that 
we are going to release noisym and noisc to the server, and to do so we need to ensure that
the currect trace iost can be broken into the past training, ios, and current training 
([e] ++ rs ++ [f]). Now we need to ensure that before running the current epoch, 
([e] ++ rs ++ [f]), we have had enough budget (count_total_budget(eps, refvalue, ios) >= k * eps)
to run the current epoch (k * eps is because k is the number of iterations in the current epoch an d
eps is the value spent on each iteration). Before starting the current epoch, we need to ensure
that we have Received the model parameters from the server (e.est == Received), 
every event in rs is Training event (all_training(rs) <=> true), lenght of rs is k, 
and finally the trained parameters are conveyed to the server (f.est == Conveyed). 

With this declassification predicate, our model is tracking just privacy budget, but it would 
be nice if we can encode some other information, e.g., connecting the noism and noisc to 
a logical function (but I don't know how difficult it would be in SecC and what can we 
prove about those logical functions)
*/
_(predicate safe_to_release_final_m_c(double noism, double noisc, double eps, double refvalue, double lrate, list<struct event> iost,
      list<struct event> ios, struct event e, list<struct event> rs, struct event f, int k)
      ((iost == append(ios, cons(e, append (rs, cons(f, nil)))) && // split the whole trace into previous ++ Received ++ latest training epoch ++ Sent
        (count_total_budget(eps, refvalue, ios) >= k * eps) && // we have enough budget to train k iterations
        e.est == Received && // received the parameters from server
        (all_training_trace(rs) <=> true) && // everything in rs is training
        (well_formed_training_trace(lrate, rs) <=> true) && // well formed training trace
        (length(rs) == k) && // k training history
        f.est == Conveyed &&  f.m == noism && f.c == noisc && // sent the trained parameters to server
        (count_total_budget(eps, refvalue, iost) >= (count_total_budget(eps, refvalue, ios) - k * eps)) ))) // during the training, we spent k * eps



/* 
This predicate connects the budget from the computational function to the 
logical function to ensure the correctness 
*/
_(predicate budget_and_trace_inv(double budget, double eps, double refvalue; list<struct event> ios)
    budget == count_total_budget(eps, refvalue, ios))

       

double compute_dE_dm(struct private_training_data *xs, int n, double m, double c)
_(requires valid_memory_inv(;xs, n))
_(ensures  valid_memory_inv(;xs, n))
{
  _(unfold valid_memory_inv(;xs, n))
  _(assert (xs == null :: low))
  if(xs == NULL)
  {
    _(assert n == 0)
    _(fold valid_memory_inv(;null, 0))
    return 0; // reached the end of xs
  }
  else
  {
    _(assert xs != null)
    _(assert (exists double u, double v, struct private_training_data *ys.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> ys && valid_memory_inv(;ys, n-1)))
    //(yi - (m * xi + c)) * xi
    double xi = xs->x;
    double yi = xs->y;
    double ans = (yi - (m * xi + c)) * xi;
    double rest = compute_dE_dm(xs->next, n-1, m, c); // n appears useless here
    _(fold valid_memory_inv(;xs, n))
    return (ans + rest);
    
  }     

}       

double compute_dE_dc(struct private_training_data *xs, int n, double m, double c)
_(requires valid_memory_inv(;xs, n))
_(ensures  valid_memory_inv(;xs, n))
{

  _(unfold valid_memory_inv(;xs, n))
  _(assert (xs == null :: low))
  if(xs == NULL)
  {
    _(assert n == 0)
    _(fold valid_memory_inv(;null, 0))
    return 0; // reached the end of xs
  }
  else
  {
    _(assert xs != null)
    _(assert (exists double u, double v, struct private_training_data *ys.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> ys && valid_memory_inv(;ys, n-1)))
    //(yi - (m * xi + c))
    double xi = xs->x;
    double yi = xs->y;
    double ans = (yi - (m * xi + c));
    double rest = compute_dE_dc(xs->next, n-1, m, c); // n appears useless here
    _(fold valid_memory_inv(;xs, n))
    return (ans + rest);
    
  }     
}




/*
This computable function computes the yhat for a given xs and m and c. The initial values of m and c are
arbitrary and as the training proceeds, the values of m and c will converge to the true values. 
yhat = m * xs + c
Y_pred = pack[0] * X + pack[1]

The only proof we have with function is that it's memory safe and does not leak any secret.
*/
void compute_yhat_from_data(double m, double c, struct private_training_data *xs, struct yvector *ys, int n)
_(requires valid_memory_inv(;xs, n))
_(requires valid_yvector_inv(;ys, n))
_(ensures  valid_memory_inv(;xs, n))
_(ensures  valid_yvector_inv(;ys, n))
{

  _(unfold valid_memory_inv(;xs, n))
  _(assert (xs == null :: low))
  if(xs == NULL)
  {
    
    _(assert n == 0)
    _(fold valid_memory_inv(;null, 0))
    return; // reached the end of xs
  }
  else
  {

    _(assert xs != null)
    _(assert n != 0)

    _(unfold valid_yvector_inv(;ys, n))
    _(assert exists double u, struct yvector *yss.
        &ys->head |-> u && (u :: high) && &ys->next |-> yss && 
        valid_yvector_inv(;yss, n-1))

    _(assert (exists double u, double v, struct private_training_data *xss.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> xss && valid_memory_inv(;xss, n-1)))
    
    ys->head = m * xs->x + c;
    compute_yhat_from_data(m, c, xs->next, ys->next, n-1);
    _(fold valid_memory_inv(;xs, n))
    _(fold valid_yvector_inv(;ys, n))
  }         

}



/*
struct to store the parameters of the model
*/
struct gradient
{
  double m;
  double c;
  struct gradient *next;
};

/*
This predicate encodes a valid memory for the gradient structure and 
n is the length of the list
*/
_(predicate valid_gradient_inv(;struct gradient *gs, int n)
   (gs == null :: low) &&
   (gs == null ? n == 0 : 
       (exists double u, double v, struct gradient *gss.
        &gs->m |-> u && (u :: high) && &gs->c |-> v && (v :: high) &&
        &gs->next |-> gss && (0 <= (n - 1)) && valid_gradient_inv(;gss, n-1))))


/*
 This computable function computes the gradient of the model for a given xs and ys, more 
 precisely, it computes the partial derivatives of the loss function with respect to the
 parameters m and c. The initial values of m and c are arbitrary and as the training
 progresses, the values of m and c will converge to the true values.
2.0 * (yhat - y) * x 
2.0 * (yhat - y)
gradient = 2.0 * np.column_stack((Y_pred - Y, Y_pred - Y)) * np.column_stack((X, np.full(n, 1.0)))
*/
void compute_gradient_m_and_c(struct yvector *yhat, struct private_training_data *xs, struct gradient *gs, int n)
_(requires valid_yvector_inv(;yhat, n))
_(requires valid_memory_inv(;xs, n))
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_yvector_inv(;yhat, n))
_(ensures  valid_memory_inv(;xs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  _(unfold valid_yvector_inv(;yhat, n))
  _(assert (yhat == null :: low))
  if(yhat == NULL)
  {
    _(assert n == 0)
    _(fold valid_yvector_inv(;null, 0))
    return; // reached the end of yhat
  }
  else
  {
    _(assert yhat != null)
    _(assert n != 0)
    _(assert exists double u, struct yvector *yss.
        &yhat->head |-> u && (u :: high) && &yhat->next |-> yss && 
        valid_yvector_inv(;yss, n-1))

    _(unfold valid_memory_inv(;xs, n))
    _(assert (exists double u, double v, struct private_training_data *xss.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> xss && valid_memory_inv(;xss, n-1)))
    
    _(unfold valid_gradient_inv(;gs, n))
    _(assert (exists double u, double v, struct gradient *gss.
        &gs->m |-> u && (u :: high) && &gs->c |-> v && (v :: high) &&
        &gs->next |-> gss && (0 <= (n - 1)) && valid_gradient_inv(;gss, n-1)))

    gs->m = 2 * (yhat->head - xs->y) * xs->x;
    gs->c = 2 * (yhat->head - xs->y);    
    compute_gradient_m_and_c(yhat->next, xs->next, gs->next, n-1);

    _(fold valid_yvector_inv(;yhat, n))
    _(fold valid_memory_inv(;xs, n))
    _(fold valid_gradient_inv(;gs, n))
  } 
}

/* Logical function from here onwards  to ensures that the constant 
time properties of computations are preserved
*/

/*
Turns a boolean value into a int value. 
false -> 0
true -> 1
*/
_(function int abs_to_pos_int(bool b))
_(rewrites
    abs_to_pos_int(false) == 0;
    abs_to_pos_int(true) == 1)


/*
Turns a boolean value into a int value.
false -> 0
true -> -1
*/
_(function int abs_to_neg_int(bool b))
_(rewrites
    abs_to_neg_int(false) == 0;
    abs_to_neg_int(true) == -1)

#if 0
/*
Proof of the correctness of the function abs_to_pos_int
is equal to -1 * abs_to_pos_int(b)
*/
void connection_between_abs_pos_neg(bool b)
_(ensures abs_to_pos_int(b) == -1 * abs_to_neg_int(b))
_(lemma) _(pure)
{
  if(b)
  {
    _(assert abs_to_pos_int(true) == 1)
    _(assert abs_to_neg_int(true) == -1)

  }
  else
  {
    _(assert abs_to_pos_int(false) == 0)
    _(assert abs_to_neg_int(false) == 0)
  }
}


/*
Logical function to compute an absolute value
of a int
*/
_(function int abs_to_int(int x))
_(rewrites
    forall int x. x >= 0 ==> (abs_to_int(x) == x);
    forall int x. x < 0 ==> (abs_to_int(x) == 0-x))




/*
Proof that the function abs_to_int is equal to the
x when x is positive 
*/
void abs_to_pint_lemma(int x)
_(requires x >= 0)
_(ensures (abs_to_int(x) == x))
_(lemma) _(pure)
{
  if(x >= 0)
  {
    _(assert (abs_to_int(x) == x))
  }

}

/*
Proof that the function abs_to_int is equal to 0 - x when 
x is negative
*/
void abs_to_nint_lemma(int x)
_(requires x < 0)
_(ensures (abs_to_int(x) == 0 - x))
_(lemma) _(pure)
{
  if(x < 0)
  {
    _(assert (abs_to_int(x) == 0 - x))
  }

}


void abs_pos_int_one(int x)
_(requires x == 1)
_(ensures abs_to_int(x) == x)
_(lemma) _(pure)
{
  
  _(assert x >= 0)
  _(apply abs_to_pint_lemma(x);)
}  

void abs_neg_int_one(int x)
_(requires x == -1)
_(ensures abs_to_int(x) == 0-x)
_(lemma) _(pure)
{
  
  _(assert x < 0)
  _(apply abs_to_nint_lemma(x);)
  _(assert abs_to_int(-1) == 0-(-1))
  _(assert abs_to_int(-1) == 1)
  
}

void abs_zero_int_one(int x)
_(requires x == 0)
_(ensures abs_to_int(x) == x)
_(lemma) _(pure)
{
 
 _(assert x >= 0)
 _(apply abs_to_pint_lemma(x);)
 _(assert abs_to_int(0) == 0)
}

void sum_of_lh(int l, int h, double m, double tau)
_(requires tau > 0)
_(requires l == abs_to_pos_int(m > tau))
_(requires h == abs_to_neg_int(m < -tau))
_(ensures (l + h == -1) || (l + h == 0) || (l + h == 1))
_(lemma) _(pure)
{
  if (m > tau)
  {
    _(assert (m > tau) == true)
    _(assert (m < -tau) == false)
    _(assert abs_to_pos_int(true) == 1)
    _(assert abs_to_neg_int(false) == 0)
    _(assert l == 1)
    _(assert h == 0)
  }
  else if (m < -tau)
  {
    _(assert abs_to_pos_int(false) == 0)
    _(assert abs_to_neg_int(true) == -1)
    _(assert l == 0)
    _(assert h == -1)
  }
  else
  {
    _(assert abs_to_pos_int(false) == 0)
    _(assert abs_to_neg_int(false) == 0)
    _(assert l == 0)
    _(assert h == 0)
  }
}

#endif


#if __SECC
int to_pos_int(bool b);
  _(ensures result == abs_to_pos_int(b))
#else
#define to_pos_int(x)  (x)
#endif


#if __SECC
int to_neg_int(bool b);
  _(ensures result == abs_to_neg_int(b))
#else
#define to_neg_int(x)  (-(x)) // to_neg_int(c<-tau) == -(c<-tau)
#endif

#if 0
void abs_pos_dual_lemma(int t, int x)
_(requires t == abs_to_pos_int(x >= 0))
_(ensures (t == 1) || (t == 0))
_(lemma) _(pure)
{
  if (x >= 0)
  {
    _(assert x >= 0 == true)
    _(assert abs_to_pos_int(true) == 1)
    _(assert t == 1)
  }
  else
  {
    _(assert x < 0)
    _(assert x >= 0 == false)
    _(assert abs_to_pos_int(false) == 0)
    _(assert t == 0)
  }
  
}

void abs_comp_lemma(int x, int t, int ret)
_(requires t == abs_to_pos_int(x >= 0))
_(requires ret == t * x + (t - 1) * x)
_(ensures ret == abs_to_int(x))
_(lemma) _(pure)
{
  if (x >= 0)
  {
    _(assert x >= 0 == true)
    _(assert abs_to_pos_int(true) == 1)
    _(assert t == 1)
    _(assert ret == x)
  }
  else
  {
    _(assert x < 0)
    _(assert x >= 0 == false)
    _(assert abs_to_pos_int(false) == 0)
    _(assert t == 0)
    _(assert ret == 0 - x)
  }
}

#endif

/*
This computable function computes the absolute value of a int
without branching and this is important because it is used to
compute the absolute value of a high value.
*/
int abs(int x)
_(ensures result == abs_to_int(x))
{
  int t = to_pos_int(x >= 0);
  _(assert t == abs_to_pos_int(x >= 0))
  _(apply abs_pos_dual_lemma(t, x);)
  _(assert t == 0 || t == 1)
  int ret = t * x + (t - 1) * x;
  _(apply abs_comp_lemma(x, t, ret);)
  _(assert ret == abs_to_int(x))

  return ret;

}

#if 0
void bounded_lemma(int l, int h, int kl, int kr, double m, double tau, double retm)
  _(requires tau > 0)
  _(requires l == abs_to_pos_int(m > tau))
  _(requires h == abs_to_neg_int(m < -tau))
  _(requires kl == l + h)
  _(requires kr == abs_to_int(kl))
  _(requires retm == (tau * kl + (1 - kr) * m))
  _(ensures  -tau <= retm && retm <= tau)
  _(lemma) _(pure)
  {

    if (m > tau)
    {
      _(assert (m > tau) == true)
      _(assert (m < -tau) == false)
      _(assert abs_to_pos_int(true) == 1)
      _(assert abs_to_neg_int(false) == 0)
      _(assert l == 1)
      _(assert h == 0)
      _(assert kl == 1)
      _(apply abs_pos_int_one(kl);)
      _(assert kr == 1)
      _(assert retm == tau)
      
    }
    else if (m < -tau)
    {
      _(assert abs_to_pos_int(false) == 0)
      _(assert abs_to_neg_int(true) == -1)
      _(assert l == 0)
      _(assert h == -1)
      _(assert kl == -1)
      _(apply abs_neg_int_one(kl);)
      _(assert kr == 1)
      _(assert retm == -tau)
    }
    else
    {
      _(assert -tau <= m && m <= tau)
      _(assert abs_to_pos_int(false) == 0)
      _(assert abs_to_neg_int(false) == 0)
      _(assert l == 0)
      _(assert h == 0)
      _(assert kl == 0)
      _(apply abs_zero_int_one(kl);)
      _(assert kr == 0)
      _(assert retm == m)
    }

  }  

#endif


/*
This computable function clips the gradient to the range [-tau, tau]
to ensure that the gradient is bounded. The proof involves that 
the gradient is free from memory error, no serect information 
is leaked, and the gradient is bounded. This implementation 
mimics the implentation of clip from numpy, except we have a proof that 
it is bounded. 
clipped_gradients = np.clip(gradients, -tau, tau)
*/

void clip_gradient(struct gradient *gs, int n, double tau)
_(requires tau > 0)
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  _(unfold valid_gradient_inv(;gs, n))
  _(assert (gs == null :: low))
  if(gs == NULL)
  {
    _(assert n == 0)
    _(fold valid_gradient_inv(;null, 0))
    return; // reached the end of gs
  }
  else
  {
    _(assert gs != null)
    _(assert n != 0)
    _(assert exists double u, double v, struct gradient *gss.
        &gs->m |-> u && (u :: high) && &gs->c |-> v && (v :: high) &&
        &gs->next |-> gss && (0 <= (n - 1)) && valid_gradient_inv(;gss, n-1))

    double m = gs->m;
    double c = gs->c;

    /*
    https://numpy.org/doc/stable/reference/generated/numpy.clip.html 
    numpy.clip(a, a_min, a_max, out=None, **kwargs)[source]

    Clip (limit) the values in an array.
    Given an interval, values outside the interval 
    are clipped to the interval edges. For example, 
    if an interval of [0, 1] is specified, values 
    smaller than 0 become 0, and values larger than
    1 become 1.
    >>> import numpy as np
    >>> in_array = [1, 2, 3, 4, 5, 6, 7, 8 ]
    >>> out_array = np.clip(in_array, 2, 5)
    >>> out_array
    array([2, 2, 3, 4, 5, 5, 5, 5])

    The idea is that we need to scale m and c 
    within [-tau, tau] because we want to avoid 
    some outliers contributing too much
    to the loss function.
    int l = m > tau ? 1 : 0;
    int h = m < -tau ? -1 : 0;
    int u = c > tau ? 1 : 0;
    int d = c < -tau ? -1 : 0;

     1. m > tau then l = 1 and h = 0 
        gs-> m = tau  
     2. m < -tau then l = 0 and h = -1
        gs-> m = -tau
     3. m < tau and m > -tau then l = 0 and h = 0
        gs-> m = m
    */
    
    int l = to_pos_int(m > tau);
    _(assert l == abs_to_pos_int(m > tau))
    int h = to_neg_int(m < -tau);
    _(assert h == abs_to_neg_int(m < -tau))
    _(apply sum_of_lh(l, h, m, tau);)
    _(assert (l + h == -1 || l + h == 0 || l + h == 1))
    
    int kl = l + h;
    _(assert kl == 0 || kl == 1 || kl == -1)
    int kr = abs(kl);
    _(assert kr == abs_to_int(kl))
    double retm = tau * kl + (1 - kr) * m;
  
    _(apply bounded_lemma(l, h, kl, kr, m, tau, retm);)
    // Proof that retm is within [-tau, tau]
    _(assert -tau <= retm && retm <= tau)
    gs->m = retm;
    
    int u = to_pos_int(c > tau);
    _(assert u == abs_to_pos_int(c > tau))
    int d = to_neg_int(c < -tau);
    _(assert d == abs_to_neg_int(c < -tau))
    _(apply sum_of_lh(u, d, c, tau);)
    _(assert (u + d == -1 || u + d == 0 || u + d == 1))

    int wl = u + d;
    _(assert wl == 0 || wl == 1 || wl == -1)
    int wr = abs(wl);
    _(assert wr == abs_to_int(wl))
    double retc = tau * wl + (1 - wr) * c;

    _(apply bounded_lemma(u, d, wl, wr, c, tau, retc);)
    // Proof that retc is within [-tau, tau]
    _(assert -tau <= retc && retc <= tau)
    gs->c = retc;    


    clip_gradient(gs->next, n-1, tau);
    _(fold valid_gradient_inv(;gs, n))
  }
}


/*
Assuming that we have clipped the gradient, now we add noise in the clipped gradient, 
we add noise to the gradients, and this off course deteriorates the perdication. 

Important: There are few ways to add noise to the gradient, e.g., in the paper
https://arxiv.org/pdf/2007.05157.pdf, the noise addition is 
(i) total_clipped_gradient = np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst)
while in the paper https://arxiv.org/pdf/1607.00133.pdf (Add Noise step in Algorithm 1) 
it is (ii) total_clipped_gradient = 1/L(np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst)), 
which after simplification is np.average(clipped_gradients, axis = 0)) + 1/L(np.random.laplace(0, 4 * tau/epst)).
In the (i) case, the authors have figured out, somehow, that storing the intermediate gradient, 
 packp = packp - l * total_clipped_gradient
 iterates[t,:] = packp, 
and making learning rate a function of error converges very fast and then in the end they average the gradients, 
return np.average(iterates[int(np.floor(T/2)):,:], axis=0) (see the python implementation DPGDPure_m_and_c,
which I have adapted from their DPGDPure, in dpgdppure.py file), while in (ii) we don't need to store any 
intermediate gradient. So, both of these implementations are equivalent. Our implementation follows (ii), and
the reason is to avoid the attacks because of doubleing point divison information leakage. Moreover, 
we don't need any auxiliary memory to store the intermediate gradient. 
*/
double sum_gradient_m(struct gradient *gs, int n)
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  _(unfold valid_gradient_inv(;gs, n))
  _(assert (gs == null :: low))
  if(gs == NULL)
  {
    _(assert n == 0)
    _(fold valid_gradient_inv(;null, 0))
    return 0; // reached the end of gs
  }
  else
  {
    _(assert gs != null)
    _(assert n != 0)
    _(assert exists double u, double v, struct gradient *gss.
        &gs->m |-> u && (u :: high) && &gs->c |-> v && (v :: high) &&
        &gs->next |-> gss && (0 <= (n - 1)) && valid_gradient_inv(;gss, n-1))

    double curr = gs->m;
    double ret = sum_gradient_m(gs->next, n-1);    
    _(fold valid_gradient_inv(;gs, n))
    return curr + ret;
  }
}

/*
Average the gradient theta1 
*/
double average_gradient_m(struct gradient *gs, int n)
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  double ret = sum_gradient_m(gs, n);
  double m = n; // I hope the compiler 
  // will take care of the division.
  return ret / m; 
   
}


/*
Sum the gradient theta2. 
*/
double sum_gradient_c(struct gradient *gs, int n)
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  _(unfold valid_gradient_inv(;gs, n))
  _(assert (gs == null :: low))
  if(gs == NULL)
  {
    _(assert n == 0)
    _(fold valid_gradient_inv(;null, 0))
    return 0; // reached the end of gs
  }
  else
  {
    _(assert gs != null)
    _(assert n != 0)
    _(assert exists double u, double v, struct gradient *gss.
        &gs->m |-> u && (u :: high) && &gs->c |-> v && (v :: high) &&
        &gs->next |-> gss && (0 <= (n - 1)) && valid_gradient_inv(;gss, n-1))

    double curr = gs->c;
    double ret = sum_gradient_m(gs->next, n-1);    
    _(fold valid_gradient_inv(;gs, n))
    return curr + ret;
  }
}

/*
Average the gradient theta2.
*/
double average_gradient_c(struct gradient *gs, int n)
_(requires valid_gradient_inv(;gs, n))
_(ensures  valid_gradient_inv(;gs, n))
{
  double ret = sum_gradient_c(gs, n);
  double m = n; // I hope the compiler 
  // will take care of the division.
  return ret / m; 
   
}

/* 
Axiomatic function to generate laplace noise, centered at 0
https://numpy.org/doc/stable/reference/random/generated/numpy.random.laplace.html
In the C program, it will be replaced by the boost library implementation.
https://www.boost.org/doc/libs/1_49_0/libs/math/doc/sf_and_dist/html/math_toolkit/dist/dist_ref/dists/laplace_dist.html
*/
double laplace_noise(double tau);
_(ensures result :: high)





// This event is triggered when server sends the model parameters to client
struct event add_receive_event_to_trace(double m, double c);
_(requires exists list<struct event> ios. io_trace(;ios))
_(ensures  result.est == Received && result.m == m && result.c == c)
_(ensures io_trace(;append(ios, cons(result, nil))))

// This event is triggered when a refill event happens. 
struct event add_refill_event_to_trace();
_(requires exists list<struct event> ios. io_trace(;ios))
_(ensures result.est == Refilled)
_(ensures io_trace(;append(ios, cons(result, nil))))


// This event triggers when training is happening. After each phase, 
// we will add noise, eps, to m and c, similar to ANoise-GD
struct event add_training_event_to_trace(double m_new, double m_old, double dm,
  double noise1, double c_new, double c_old, double dc, double noise2, double learning_rate);
_(requires exists list<struct event> ios. io_trace(;ios))
_(ensures  result.est == Training && result.m == m_new  && 
    result.m_old == m_old && result.dm == dm && result.noise1 == noise1 &&
    result.c == c_new && result.c_old == c_old && result.dc == dc &&
    result.noise2 == noise2)
_(ensures m_new == m_old - learning_rate * (dm + noise1))
_(ensures c_new == c_old - learning_rate * (dc + noise2))
_(ensures io_trace(;append(ios, cons(result, nil))))


// This event is triggered when client sends the model 
// parameters to server
struct event add_conveyed_event_to_trace(double m, double c);
_(requires exists list<struct event> ios. io_trace(;ios))
_(ensures  result.est == Conveyed && result.m == m && result.c == c)
_(ensures io_trace(;append(ios, cons(result, nil))))



// Beginning of the process when we start a client
status_code start_the_client(double *budget, double eps, double refvalue)
_(requires io_trace(;nil))
_(requires  0 < eps)
_(requires exists double val. budget |-> val)
_(ensures result == Success)
_(ensures budget |-> 0)
_(ensures budget_and_trace_inv(0, eps, refvalue; nil))
_(ensures io_trace(;nil))
{
  *budget = 0;
  _(assert 0 == count_total_budget(eps, refvalue, nil))
  _(fold budget_and_trace_inv(0, eps, refvalue; nil))
  return Success;
}

#if 0
void budget_append(double eps, double refvalue, list<struct event> ls, list<struct event> rs)
_(ensures count_total_budget(eps, refvalue, append(ls, rs)) == 
    (count_total_budget(eps, refvalue, ls) + count_total_budget(eps, refvalue, rs)))
_(lemma) _(pure)
{
  if(ls != nil)
  {
    _(assert exists struct event x, list<struct event> xs. ls == cons(x, xs))
    budget_append(eps, refvalue, xs, rs);
  }
}

void adding_refill_to_trace(double obudget, double eps, double refvalue, struct event e, list<struct event> ios)
_(requires e.est == Refilled)
_(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
_(ensures budget_and_trace_inv(obudget+refvalue, eps, refvalue; append(ios, cons(e, nil))))
_(lemma)
{
  _(unfold budget_and_trace_inv(obudget, eps, refvalue; ios))
  _(assert obudget == count_total_budget(eps, refvalue, ios))
  _(assert count_total_budget(eps, refvalue, cons(e, nil)) == refvalue)
  _(apply budget_append(eps, refvalue, ios, cons(e, nil));)
  _(assert count_total_budget(eps, refvalue, append(ios, cons(e, nil))) == 
      (count_total_budget(eps, refvalue, ios) + count_total_budget(eps, refvalue, cons(e, nil))))
  _(fold budget_and_trace_inv(obudget + refvalue, eps, refvalue; append(ios, cons(e, nil))))
}
#endif

/*
This function is called in the beginning to fill the budget. 
*/
status_code fill_budget(double *budget, double eps, double refvalue)
_(requires exists list<struct event> ios. io_trace(;ios))
_(requires 0 < eps)
_(requires exists double obudget. budget |-> obudget)
_(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
_(ensures result == Success)
_(ensures budget |-> obudget + refvalue) 
_(ensures exists struct event e. e.est == Refilled)
_(ensures exists list<struct event> iost. iost == append(ios, cons(e, nil)) && io_trace(;iost))
_(ensures budget_and_trace_inv(obudget + refvalue, eps, refvalue; iost))
{
  *budget = *budget + refvalue;
  struct event e = add_refill_event_to_trace();
  _(assert e.est == Refilled)
  _(assert io_trace(;append(ios, cons(e, nil))))
  _(apply adding_refill_to_trace(obudget, eps, refvalue, e, ios);)
  return Success;
}


/*
Thoughts: can I prove that at every step of Gradient Descent, the new value of m and c minimises
the error and therefore it reaches the minima. How difficult it would be? And more importantly, 
can it be proved? 
*/

_(function int length(list<struct event> ios))
_(rewrites 
    length(nil) == 0;
    forall struct event x, list<struct event> xs. 
       length(cons(x, xs)) == 1 + length(xs))

#if 0
void append_list_lemma(list<struct event> ios, struct event e1, struct event e2)
_(ensures append(append(ios, cons(e1, nil)), cons(e2, nil)) == append(ios, cons(e1, cons(e2, nil))))
_(lemma) _(pure)
{
  if (ios == nil)
  {
    // we are home
    _(assert append(append(nil, cons(e1, nil)), cons(e2, nil)) == 
        append(cons(e1, nil), cons(e2, nil)))
    _(assert append(nil, cons(e1, cons(e2, nil))) == 
        append(cons(e1, nil), cons(e2, nil)))
    _(assert append(append(nil, cons(e1, nil)), cons(e2, nil)) == 
        append(nil, cons(e1, cons(e2, nil))))
    return;
  }
  else
  {
    _(assert exists struct event y, list<struct event> ys. ios == cons(y, ys))
    _(assert append(append(cons(y, ys), cons(e1, nil)), cons(e2, nil)) == 
        cons(y, append(append(ys, cons(e1, nil)), cons(e2, nil))))
    _(assert append(cons(y, ys), cons(e1, cons(e2, nil))) == 
        cons(y, append(ys, cons(e1, cons(e2, nil)))))
    append_list_lemma(ys, e1, e2);
    _(assert append(append(ys, cons(e1, nil)), cons(e2, nil)) == append(ys, cons(e1, cons(e2, nil))))

  }
  
}

void append_associative_lemma(list<struct event> l1, list<struct event> l2, list<struct event> l3)
_(ensures append(append(l1, l2), l3) == append(l1, append(l2, l3)))
_(pure) _(lemma)
{
  if(l1 == nil)
  {
    _(assert append(l2, l3) == append(l2, l3))
    return;
  }
  else
  {
    _(assert exists struct event x, list<struct event> xs. l1 == cons(x, xs))
    append_associative_lemma(xs, l2, l3);
    return;
  }

}

void budget_append_preserve(double eps, double refvalue, list<struct event> ls, list<struct event> rs)
_(ensures count_total_budget(eps, refvalue, append(ls, rs)) == 
    (count_total_budget(eps, refvalue, ls) + count_total_budget(eps, refvalue, rs)))
_(lemma) _(pure)
{

  if(ls == nil)
  {
    // we are home (base case)
    _(assert append(nil, rs) == rs)
    _(assert count_total_budget(eps, refvalue, append(ls, rs)) == 
          count_total_budget(eps, refvalue, rs))
    
    _(assert count_total_budget(eps, refvalue, ls) == 0)
    return;
  }
  else
  {
    // inductive case
    _(assert exists struct event x, list<struct event> xs. ls == cons(x, xs))
    _(assert count_total_budget(eps, refvalue, append(cons(x, xs), rs)) == 
         count_total_budget(eps, refvalue, cons(x, nil)) + 
         count_total_budget(eps, refvalue, append(xs, rs)))
    budget_append(eps, refvalue, xs, rs);
    _(assert count_total_budget(eps, refvalue, append(xs, rs)) == 
         count_total_budget(eps, refvalue, xs) + 
         count_total_budget(eps, refvalue, rs))
  }
}

void no_training_no_budget_spent(list<struct event> iost2, list<struct event> ios, struct event e, struct event et2, int obudget, double eps, double refvalue)
 _(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
 _(requires e.est == Received && et2.est == Conveyed)
 _(requires iost2 == append(ios, append(cons(e, nil), cons(et2, nil))))
 _(ensures budget_and_trace_inv(obudget, eps, refvalue; iost2))
 _(lemma) _(pure)
 {

   _(unfold budget_and_trace_inv(obudget, eps, refvalue; ios))
   _(assert obudget == count_total_budget(eps, refvalue, ios))
   _(apply append_list_lemma(ios, e, et2);)
   _(assert iost2 == append(ios, cons(e, cons(et2, nil))))
   _(assert exists list<struct event> ioe. ioe == cons(e, cons(et2, nil)))
   _(assert count_total_budget(eps, refvalue, cons(e, cons(et2, nil))) == 0)
   _(apply budget_append_preserve(eps, refvalue, ios, ioe);)
   _(assert count_total_budget(eps, refvalue, iost2) == 
      (count_total_budget(eps, refvalue, ios)))
   _(assert obudget == count_total_budget(eps, refvalue, iost2))
    _(fold budget_and_trace_inv(obudget, eps, refvalue; iost2))

 }

 void append_nil(list<struct event> ios)
 _(ensures append(ios, nil) == ios)
 _(lemma) _(pure)
 {
   if(ios == nil)
   {
     return;
   }
   else
   {
     _(assert exists struct event e, list<struct event> es. ios == cons(e, es))
     append_nil(es);
     return;
   }
   
 }

 void append_append_nil(list<struct event> ios, struct event e, list<struct event> iotl)
 _(ensures  (append(append(ios, cons(e, nil)), iotl) == append(ios, cons(e, iotl))))
 _(lemma) _(pure)
 {
   if(ios == nil)
   {
     return;
   }
   else
   {
     _(assert exists struct event et, list<struct event> es. ios == cons(et, es))
     append_append_nil(es, e, iotl);
     
   }
   
 }

void length_append(list<struct event> ios, struct event et)
 _(ensures length(append(ios, cons(et, nil))) == length(ios) + 1)
 _(lemma) _(pure)
 {
   if(ios == nil)
   {
     return;
   }
   else
   {
     _(assert exists struct event e, list<struct event> es. ios == cons(e, es))
     length_append(es, et);
     
   }
   
 }

_(function bool all_training_trace(list<struct event> ios))
_(rewrites
     all_training_trace(nil) <=> true;
     forall struct event e, list<struct event> es. 
      all_training_trace(cons(e, es)) <=> 
      ((e.est == Training) && all_training_trace(es)))

/*

This function ensures that the trace, generate during the training, is "well-formed"

*/
_(function bool well_formed_training_trace(double learn_rate, list<struct event> ios))
_(rewrites
    forall double learn_rate. well_formed_training_trace(learn_rate, nil) <=> true; // no training
    forall double learn_rate, struct event e, list<struct event> es. 
      well_formed_training_trace(learn_rate, cons(e, es)) <=>
      ((e.est == Training && (e.m == (e.m_old - learn_rate * (e.dm + e.noise1))) && 
       (e.c == (e.c_old - learn_rate * (e.dc + e.noise2)))) && 
       well_formed_training_trace(learn_rate, es)))



    
void length_append_general(list<struct event> l1, list<struct event> l2)
_(ensures length(append(l1, l2)) == length(l1) + length(l2))
_(lemma) _(pure)
{
  if(l1 == nil)
  {
    return;
  }
  else
  {
    _(assert exists struct event e, list<struct event> es. l1 == cons(e, es))
    length_append_general(es, l2);
  }
  
}

void length_proof(list<struct event> l1, list<struct event> l2, list<struct event> l3, int k)
_(requires l1 == append(l2, l3))
_(requires length(l1) == length(l2) + k)
_(ensures length(l3) == k)
_(lemma) _(pure)
{
  _(apply length_append_general(l2, l3);)
  _(assert length(append(l2, l3)) == length(l2) + length(l3))
  _(assert length(l1) == length(l2) + length(l3))
  _(assert length(l1) == length(l2) + k)
  _(assert length(l3) == k)
  return;

}

#endif



/*
In this framework, developers can plug their neural network, linear regression, or whatever 
is in faishon. They don't need to bother about budget tracking because we have already proved 
that when their is not enpught budget, the it would not train.  More importantly, we generate 
evidence, in terms of data, that can be used by any third party to audit the claim of a client.
*/  
void recursive_gradient_descent(int k, struct  private_training_data *xs, int n, double *m, double *c, 
  double *learning_rate, double *budget, double eps, double refvalue, struct yvector *yhat, struct gradient *gs)
_(requires k >= 0 && k :: low)
_(requires valid_yvector_inv(;yhat, n)) 
_(requires valid_memory_inv(;xs, n))
_(requires valid_gradient_inv(;gs, n))
_(requires exists list<struct event> ios. io_trace(;ios))
_(requires 0 < eps && eps :: low)
_(requires exists double obudget. 
    budget |-> obudget && obudget :: low)
_(requires obudget >= k * eps)
_(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
_(requires exists double lrate. 
    learning_rate |-> lrate)
_(requires exists double oldm. m |-> oldm)
_(requires exists double oldc. c |-> oldc)
_(requires exists struct event ew, list<struct event> iosw.
   ios == append(iosw, cons(ew, nil)) && ew.m == oldm &&
   ew.c == oldc)
_(ensures  valid_memory_inv(;xs, n))
_(ensures  exists double newm. m |-> newm)
_(ensures  exists double newc. c |-> newc)
_(ensures  budget |-> (obudget - k * eps) && (obudget - k * eps) >= 0)
_(ensures  learning_rate |-> lrate)
_(ensures  exists list<struct event> iotr. io_trace(;iotr))
_(ensures  exists struct event ewt, list<struct event> ioswt.
    iotr == append(ioswt, cons(ewt, nil)) && ewt.m == newm &&
    ewt.c == newc)
_(ensures  budget_and_trace_inv((obudget - k * eps), eps, refvalue; iotr))
_(ensures  length(iotr) == length(ios) + k)
_(ensures  exists list<struct event> iotl. 
   iotr == append(ios, iotl) &&
   (append(ioswt, cons(ewt, nil)) == append(append(iosw, cons(ew, nil)), iotl)) &&
   (all_training_trace(iotl) <=> true) &&
   (well_formed_training_trace(lrate, iotl) <=> true) &&
   (count_total_budget(eps, refvalue, iotl) == -k * eps))
_(ensures valid_yvector_inv(;yhat, n))
_(ensures valid_gradient_inv(;gs, n))
{

  if (k == 0)
  {
    
    // we have reached the end
    // do nothing and simply return
    _(assert k == 0)
    _(assert exists list<struct event> iotr. iotr == ios)
    _(assert exists list<struct event> iotl. iotl == nil)
    _(apply append_nil(ios);)
    _(assert iotr == append(ios, nil))
    _(assert all_training_trace(iotl) <=> true)
    _(assert well_formed_training_trace(lrate, iotl) <=> true)
    _(assert count_total_budget(eps, refvalue, iotl) == -k * eps)
    
    return;
  }
  else
  {
    double m_old;
    double c_old;
    double m_new;
    double c_new;
    double learn_rate;
    double cbudget;
    double dm; 
    double dc;  
    
    m_old = *m;
    c_old = *c;
    learn_rate = *learning_rate;
    cbudget = *budget;

    _(unfold budget_and_trace_inv(obudget, eps, refvalue; ios))
    _(assert obudget == count_total_budget(eps, refvalue, ios))
    _(assert cbudget == obudget)

    /* any generic machine learning code can 
      be plugged here to track the budget. 
      In our case, it is linear regression 
      but there is nothing stopping us from 
      plgging anything else. */
    // yhat = m * xs + c
    // Y_pred = pack[0] * X + pack[1]
    // We are going to predicate Yhat from 
    // so far computer gradients, i.e., m_old and c_old.
    // and the value of Yhat will be stored in ys.    
    compute_yhat_from_data(m_old, c_old, xs, yhat, n);

    // Now that I have yhat, let's compute the gradient.
    // computer the gradient
    // 2.0 * (yhat - y) * x 
    // 2.0 * (yhat - y)
    // gradient = 2.0 * np.column_stack((Y_pred - Y, Y_pred - Y)) * np.column_stack((X, np.full(n, 1.0)))
    // void compute_gradient_m_and_c(struct yvector *yhat, struct private_training_data *xs, struct gradient *gs, int n)
    compute_gradient_m_and_c(yhat, xs, gs, n);

    double tau = 1; // 1.0 is parse error
    // Now clip the gradient
    clip_gradient(gs, n, tau);

    // Assuming that we have clipped the gradient,
    // we need to add noise to the gradient.
    // total_clipped_gradient = np.average(clipped_gradients, axis = 0) + 
    // np.random.laplace(0, 4 * tau/epst)/n
    double noise1 = laplace_noise(4 * tau/eps)/n;
    double noise2 = laplace_noise(4 * tau/eps)/n;

    // Notes: one problem is that we can't use the doubleing point division because
    // of timing attack. Therefore, our learning rate is constant. 
    // total_clipped_gradient = (np.sum(clipped_gradients, axis = 0) + np.random.laplace(0, 4 * tau/epst))/n 
    // which corresponds to line add noise in Different Private SGD paper, https://arxiv.org/pdf/1607.00133.pdf%20.
    // After simplification and pushing the n inside, we get 
    // total_clipped_gradient = np.average(clipped_gradients, axis = 0) + (np.random.laplace(0, 4 * tau/epst)/n).
    dm = average_gradient_m(gs, n);
    dc = average_gradient_c(gs, n);

    //Now compute the new gradient
    //pack = pack - l * total_clipped_gradient
    m_new = m_old - learn_rate * (dm + noise1);
    c_new = c_old - learn_rate * (dc + noise2);



    cbudget = cbudget - eps;
    _(assert cbudget == obudget - eps)
    *m = m_new;
    *c = c_new;
    *budget = cbudget;
    
    // Record all the data that captures the learning
    struct event et = add_training_event_to_trace(m_new, m_old, dm, noise1, 
      c_new, c_old, dc, noise2, learn_rate);
    
    _(assert et.est == Training && et.m == m_new && et.m_old == m_old && et.dm == dm && et.noise1 == noise1 &&
      et.c == c_new && et.c_old == c_old && et.dc == dc && et.noise2 == noise2)
    _(assert exists struct event ew, list<struct event> iosw. ios == append(iosw, cons(ew, nil)) && ew.m == m_old)
    _(assert exists list<struct event> iost. iost == append(ios, cons(et, nil)) &&
      io_trace(;iost))

    //This epoch has cost eps. 
    _(assert count_total_budget(eps, refvalue, cons(et, nil)) == -eps)
    _(apply budget_append_preserve(eps, refvalue, ios, cons(et, nil));)
    _(assert count_total_budget(eps, refvalue, iost) == 
           (-eps) + count_total_budget(eps, refvalue, ios))
    _(fold budget_and_trace_inv(obudget-eps, eps, refvalue; iost))

    recursive_gradient_descent(k-1, xs, n, m, c, learning_rate, budget, eps, refvalue, yhat, gs);
    
    _(assert exists list<struct event> iotr. io_trace(;iotr))
    _(assert exists struct event ewt, list<struct event> ioswt. 
        iotr == append(ioswt, cons(ewt, nil)))
    _(assert length(iotr) == length(iost) + (k - 1))
    _(apply length_append(ios, et);)
    _(assert length(iost) == length(ios) + 1)
    _(assert length(iotr) == length(ios) + k)
    _(assert exists list<struct event> iotl.
       iotr == append(iost, iotl) &&
       ios == append(iosw, cons(ew, nil)) &&
       iotr == append(append(ios, cons(et, nil)), iotl) &&
       (all_training_trace(iotl) <=> true) &&
       (well_formed_training_trace(lrate, iotl) <=> true) &&
       (count_total_budget(eps, refvalue, iotl) == -(k-1) * eps))
    _(apply append_append_nil(ios, et, iotl);)
    _(assert iotr == append(ios, cons(et, iotl)))
    _(assert iotr == append(ioswt, cons(ewt, nil)))
    _(assert append(ioswt, cons(ewt, nil)) == append(ios, cons(et, iotl)))
    _(assert (all_training_trace(cons(et, iotl)) <=> true))
    _(assert (well_formed_training_trace(lrate, cons(et, iotl)) <=> true))
    _(assert count_total_budget(eps, refvalue, cons(et, iotl)) == -k * eps)
    
    
    return;

  }

}



/*
Idea: we are developing a information flow framework, equipped with noise addition (differential privacy), 
that would ensure the secure learning, without leaking any private information. In this framework, 
a server would send the parameters to a client and client will train the parameter on its secret 
data and return it to the server.
*/

// m and c are used for receiving, and mret and cret are used for sending  
status_code predict_m_and_c_using_grad_descent(struct  private_training_data *xs, int n, double *m, double *c,
  double *mret, double *cret, double *learning_rate, double *budget, double eps, double refvalue, int k, struct yvector *yhat, struct gradient *gs)
  _(requires valid_memory_inv(;xs, n))
  _(requires valid_yvector_inv(;yhat, n))
  _(requires valid_gradient_inv(;gs, n))
  _(requires exists list<struct event> ios. io_trace(;ios))
  _(requires k >= 0 && k :: low)
  _(requires 0 < eps && eps :: low)
  _(requires exists double obudget. budget |-> obudget && obudget :: low)
  _(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
  _(requires exists double lrate. learning_rate |-> lrate)
  _(requires exists double oldm. m |-> oldm)
  _(requires exists double oldc. c |-> oldc)
  _(requires exists double oldmret. mret |-> oldmret && oldmret :: low)
  _(requires exists double oldcret. cret |-> oldcret && oldcret :: low)
  _(ensures  result :: low)
  _(ensures  valid_memory_inv(;xs, n))
  _(ensures  exists double newm. m |-> newm)
  _(ensures  exists double newc. c |-> newc)
  _(ensures  exists double nmret. mret |-> nmret && nmret :: low)
  _(ensures  exists double ncret. cret |-> ncret && ncret :: low)
  _(ensures  exists double newb. budget |-> newb && newb :: low)
  _(ensures  learning_rate |-> lrate)
  _(ensures  exists list<struct event> iost. io_trace(;iost))
  _(ensures  budget_and_trace_inv(newb, eps, refvalue; iost))
  _(ensures result == Failure ==> newm == oldm && newc == oldc && 
      newb == obudget)
  _(ensures result == Failure ==> oldmret == nmret && oldcret == ncret)
  _(ensures result == Success ==> nmret == newm && ncret == newc)        
  _(ensures result == Success ==> newb == (obudget - k * eps))
  _(ensures valid_yvector_inv(;yhat, n))
  _(ensures valid_gradient_inv(;gs, n))    
  {
    _(unfold budget_and_trace_inv(obudget, eps, refvalue; ios))
    // received event
    double m_old = *m;
    double c_old = *c;
    double learn_rate = *learning_rate;
    struct event e = add_receive_event_to_trace(m_old, c_old);
    _(assert  e.est == Received && e.m == m_old && e.c == c_old)
    _(assert exists list<struct event> iost. iost == append(ios, cons(e, nil)) &&
        io_trace(;iost))

    
    _(assert count_total_budget(eps, refvalue, cons(e,nil)) == 0)
    _(assert iost == append(ios, cons(e, nil)))
    _(apply budget_append_preserve(eps, refvalue, ios, cons(e, nil));)
    _(assert count_total_budget(eps, refvalue, iost) == 
            count_total_budget(eps, refvalue, ios))
    _(fold budget_and_trace_inv(obudget, eps, refvalue; iost))    

    // connection between generating noise and privacy budget
    // check if we have enought privacy budget for training
    // if yes, Train and if no, return the values received 
    // from the server. 
    double cbudget = *budget;
    _(assert cbudget == obudget)

    // we have enough budget to run 
    // k iterations of training
    if (cbudget >= k * eps)
    {

      _(assert budget_and_trace_inv(obudget, eps, refvalue; iost))

      recursive_gradient_descent(k, xs, n, m, c, learning_rate, budget, eps, refvalue, yhat, gs);
      
      _(assert exists list<struct event> iostr. 
         budget_and_trace_inv(obudget - k * eps, eps, refvalue; iostr))
      _(assert length(iostr) == length(iost) + k)
      _(assert exists list<struct event> iotl. iostr == append(iost, iotl) &&
        (all_training_trace(iotl) <=> true) &&
        (well_formed_training_trace(learn_rate, iotl) <=> true))

      _(apply length_proof(iostr, iost, iotl, k);)
      _(assert length(iotl) == k)
         
      m_old = *m; 
      c_old = *c;
      
      struct event et1 = add_conveyed_event_to_trace(m_old, c_old);
      _(assert et1.est == Conveyed && et1.m == m_old && et1.c == c_old)
      _(assert exists list<struct event> iost2. iost2 == append(iostr, cons(et1, nil)) &&
           io_trace(;iost2))
      _(unfold budget_and_trace_inv(obudget - k * eps, eps, refvalue; iostr))
      _(assert (obudget - k * eps) >= 0)
      _(assert (obudget - k * eps) == count_total_budget(eps, refvalue, iostr))
      _(assert count_total_budget(eps, refvalue, cons(et1, nil)) == 0)
      _(apply budget_append_preserve(eps, refvalue, iostr, cons(et1, nil));)
      _(assert count_total_budget(eps, refvalue, iost2) == 
               count_total_budget(eps, refvalue, iostr))         
      _(fold budget_and_trace_inv(obudget - k * eps, eps, refvalue; iost2))
      _(assert budget_and_trace_inv(obudget - k * eps, eps, refvalue; iost2))


      _(apply append_append_nil(ios, e, iotl);)
      _(assert append(append(ios, cons(e, nil)), iotl) == append(ios, cons(e, iotl)))
      _(assert (append(append(append(ios, cons(e, nil)), iotl), cons(et1, nil))) == 
               (append(append(ios, cons(e, iotl)), cons(et1, nil))))
      _(assert append(cons(e, iotl), cons(et1, nil)) == cons(e, append(iotl, cons(et1, nil))))
      _(apply append_associative_lemma(ios, cons(e, iotl), cons(et1, nil));)
      _(assert (append(append(ios, cons(e, iotl)), cons(et1, nil))) == 
               (append(ios, cons(e, append(iotl, cons(et1, nil))))))

      // preparation of declassification
      _(assert iost2 == append(ios, cons(e, append(iotl, cons(et1,nil)))))
      _(assert count_total_budget(eps, refvalue, ios) >= k * eps)
      _(assert count_total_budget(eps, refvalue, iost2) >= (count_total_budget(eps, refvalue, ios) - k * eps))
      _(assert e.est == Received)
      _(assert all_training_trace(iotl) <=> true)
      _(assert length(iotl) == k)
      _(assert et1.est == Conveyed && et1.m == m_old && et1.c == c_old)
      _(fold safe_to_release_final_m_c(m_old, c_old, eps, refvalue, learn_rate, iost2, ios, e, iotl, et1, k))
      // now we can safely release the noisy m and noisy c that 
      // was computed by gradient descent. 

      *mret = m_old;
      *cret = c_old;
      
      _(assume m_old :: low && c_old :: low)
      _(unfold safe_to_release_final_m_c(m_old, c_old, eps, refvalue, learn_rate, iost2, ios, e, iotl, et1, k))
      
      
      return Success; 
    }
    else
    {
      // Just return whatever we have 
      // received and add a trace to the
      // program history 
      
      _(unfold budget_and_trace_inv(obudget, eps, refvalue; iost))
      _(assert obudget == count_total_budget(eps, refvalue, iost))
      _(assert iost == append(ios, cons(e, nil)))
      _(assert count_total_budget(eps, refvalue, iost) == 
            count_total_budget(eps, refvalue, ios))
      struct event et2 = add_conveyed_event_to_trace(m_old, c_old);
      _(assert et2.est == Conveyed && et2.m == m_old && et2.c == c_old)
      _(assert exists list<struct event> iost2. iost2 == append(iost, cons(et2, nil)))
      
      _(assert count_total_budget(eps, refvalue, cons(et2, nil)) == 0)
      _(apply budget_append_preserve(eps, refvalue, iost, cons(et2, nil));)
      _(assert count_total_budget(eps, refvalue, iost2) == 
             count_total_budget(eps, refvalue, iost))
      _(assert count_total_budget(eps, refvalue, iost) == count_total_budget(eps, refvalue, ios))
      _(assert count_total_budget(eps, refvalue, iost2) == count_total_budget(eps, refvalue, ios))
      _(fold budget_and_trace_inv(cbudget, eps, refvalue; iost2))
      return Failure;
    }
    
  }



double *budget;
double eps; 
double refvalue;
struct  private_training_data *xs;
struct yvector *ys;
struct gradient *gs;
int n;
double *m;
double *c;
double *mret; 
double *cret;
double *learning_rate;
int k;

void sleep(int delay);
_(requires delay :: low)


/* lock acquire */
void acquire_lock();
_(ensures exists list<struct event> ios. io_trace(;ios))
_(ensures exists double obudget. budget |-> obudget && obudget :: low)
_(ensures budget_and_trace_inv(obudget, eps, refvalue; ios))
_(ensures refvalue :: low)
_(ensures 0 < eps && eps :: low)
_(ensures valid_memory_inv(;xs, n))
_(ensures valid_yvector_inv(;ys, n))
_(ensures valid_gradient_inv(;gs, n))
_(ensures exists double lrate. learning_rate |-> lrate)
_(ensures exists double oldm. m |-> oldm)
_(ensures exists double oldc. c |-> oldc)
_(ensures 0 <= k && k :: low)
_(ensures exists double oldmret. mret |-> oldmret && oldmret :: low)
_(ensures exists double oldcret. cret |-> oldcret && oldcret :: low)
  
/* release lock */
void release_lock();
_(requires exists list<struct event> ios. io_trace(;ios))
_(requires exists double obudget. budget |-> obudget && obudget :: low)
_(requires budget_and_trace_inv(obudget, eps, refvalue; ios))
_(requires refvalue :: low)
_(requires 0 < eps && eps :: low)
_(requires valid_memory_inv(;xs, n))
_(requires valid_yvector_inv(;ys, n))
_(requires valid_gradient_inv(;gs, n))
_(requires exists double lrate. learning_rate |-> lrate)
_(requires exists double oldm. m |-> oldm)
_(requires exists double oldc. c |-> oldc)
_(requires 0 <= k && k :: low)
_(requires exists double oldmret. mret |-> oldmret && oldmret :: low)
_(requires exists double oldcret. cret |-> oldcret && oldcret :: low)


void print_gradient(status_code t, double m, double c);


/* 
this thread runs the machine learning algorithm
on clients. Clients receive the parameter from 
server in m and c, run the algorithm and send 
the modified parameter in mret and cret
*/
status_code run_the_learning_framework()
{
    acquire_lock();
    status_code t = predict_m_and_c_using_grad_descent(xs, n, m, c, mret, cret, learning_rate, budget, eps, refvalue, k, ys, gs);
    print_gradient(t, *mret, *cret);
    release_lock();
    //sleep(5);
    return t;
}
