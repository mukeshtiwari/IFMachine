#include "secc.h"


/*
The high level idea is:
Server would send the model parameters to clients, 
and the clients would train/refine the model
parameters and send it back to the server, 
where it will update the model parameter and 
the process goes on. 

Operational Details:
Every client will record events to encode 
the declassification predicate. Moreover, 
it can also be used as history to audit 
the client. A client would start with 
some budget and during the training, 
it will spend it. Once, the budget is 
finished, it will stop training until 
the budget is replenished.  The advantage 
of this design is (i) we can use our 
threading system to replenish the client and 
(ii) even if the server wants to attack a 
particular client by sendning the model parameter 
more frequently to gain some information, 
it cannot do so because the client will 
run out of the training budget and 
not replenished until the replenish-thread
fills the buget after a fixed amount of time. 
In a nutshell, a malicious server cannot 
exploit clients to extract any information
(Find some literature where attacks like this 
are mentioned in the Federated Learning) 

Using this system, we also solve the problem 
of hetrogeneous devices because a small 
device can set its time duration of replenish 
more than a computer (48 hours vs 12 hours)
(Find a literature to support this claim)

*/





typedef int float; // Reasoning for float by plugging Alan's code?
// However, there are some caveats with Alan's floating point 
// reasoning. It assumes, based on my understanding of Alan's 
// presentation, that float value should be public; however, 
// in this case, the observations, for the moment just two point 
// and we are using linear regression using gradient descent, 
// are secrets, which will be disallowed by Alan's  reasoning
// code. 

struct list 
  {
    float x;
    float y;
    struct list *next;
  };


/*
This enum represents an event. 
Received represents the parameter received 
from server
Training represents the client running
the training on a give data with the parameters
received in the Received phase; 
Conveyed represents the final parameters update 
to the server. */
enum ev_status
{
  Received,
  Training,
  Conveyed,
  Refilled
};
typedef enum ev_status event_status;

/*
This enum represents if a function failed or succeed
*/
enum ret_code 
{
  Failure, // if a client is out of budget, it will simply return the received model parameters to server 
  Success // if a client has budge, it will train 
};
typedef enum ret_code status_code;


struct event
{
  event_status est;
  float m; // model parameter  
  float c; // model parameter  
  // float noise; // amount of noise added 
  //  in each step of training https://arxiv.org/pdf/1405.7085.pdf
};


/* 
Input-Output history modelled as list, and this 
list contains enough information (snap shot of various
variables during the program execution) to ensure 
the declassification. 
*/
_(predicate io_trace(;list<struct event> xs))


// It's a relational predicate
// Inductive Valid_mem_inv 
// Empty : Valid_mem_inv nil 0 
// Cons y ys n : Valid_mem_inv ys n -> Valid_mem_inv (y :: ys) (n + 1)
_(predicate valid_memory_inv(;struct list *xs, int n)
   (xs == null :: low) &&
   (xs == null ? n == 0 : 
       (exists float u, float v, struct list *ys.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> ys && valid_memory_inv(;ys, n-1))))

/*
Model the memory as Array. 
_(predicate ar(int *a, int i, int j)
	i < j ==> exists int x. &a[i] |-> x && ar(a, i+1, j))

We can access any location but, at this point, I am not sure if 
we need it. However, I am keeping it as an option. 
*/


/* 
Idea is to compute linear regression using gradient descent [1] and 
improvise upon this idea to encode other sophasticated, e.g., 
stochastic gradient descent [2], and finally differential private 
stochastic gradeint descent [3]. Once we have DP-SGD, then 
we plug it for existing case study of federated learning. 
This is going to be an awesome project and publication to CCS 
because no one has tried to formalise the DP-Federated Learning 
from information flow perspective. 

[1] https://towardsdatascience.com/linear-regression-using-gradient-descent-97a6c8700931
[2] https://realpython.com/gradient-descent-algorithm-python/
[3] https://medium.com/pytorch/differential-privacy-series-part-1-dp-sgd-algorithm-explained-12512c3959a3
*/

/* 
Loss function as function pointer? 
*/

/*
Ramblings:
  Can we prove some of these Lemmas, Definitions [1]? 
  For example, it would be interesting to prove that 
  our function f is smooth and convex. Some of 
  the issues are that these concepts are defined 
  for real numbers and we are using float. In practice, 
  floats approximates real numbers.
  [1] https://gowerrobert.github.io/pdf/M2_statistique_optimisation/grad_conv.pdf


More idea, can we use these logical functions to prove the 
smoothness and convexity. Moreover, we can define an closed 
expression derivative of function and show that the 
analytical solution, gradient descent, converges to it, but how?
I don't have idea at this point. 

Question: But everything I said above, assumed no noise addition during 
the training, so what can we prove about the DP-SGD model. It's getting 
more and more challenging. 
  */


// proof that y = m * x + c, which we are using currently as a predictor,  
// is a convex function
void convexity_proof(float m, float c, int t, float x, float y)
  _(requires t == 0 || t == 1)
  _(ensures (m * (t * x + (1 - t) * y) + c) <= t * (m * x + c) + (1 - t) * (m * y + c))
  _(lemma) _(pure)
  {
   if (t == 0)
   {
     _(assert (m * y + c) <= (m * y + c))
   }
   else 
   {
     _(assert t == 1)
     _(assert m * x + c <= (m * x + c))
   }
  }



_(function float logical_compute_dE_dm(list<struct list> xs, float m, float c))
_(rewrites
    forall float m, float c. logical_compute_dE_dm(nil, m, c) == 0;
    forall float m, float c, struct list v, list<struct list> vs. 
      logical_compute_dE_dm(cons(v, vs), m, c) == 
      (((v.y - (m * v.x + c)) * v.x) + logical_compute_dE_dm(vs, m, c))) 
  

_(function float logical_compute_dE_dc(list<struct list> xs, float m, float c))
_(rewrites
    forall float m, float c. logical_compute_dE_dc(nil, m, c) == 0;
    forall float m, float c, struct list v, list<struct list> vs. 
      logical_compute_dE_dc(cons(v, vs), m, c) == 
      ((v.y - (m * v.x + c)) + logical_compute_dE_dc(vs, m, c))) 


float compute_dE_dm(struct list *xs, int n, float m, float c)
_(requires valid_memory_inv(;xs, n))
_(ensures  valid_memory_inv(;xs, n))
// we can find a logical list ls, and connect it to 
// xs and show that the value returned by this function is same 
// as the value returned by the logical counterpart, logical_compute_dE_dm.
// But what extra value we will get? 
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
    _(assert (exists float u, float v, struct list *ys.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> ys && valid_memory_inv(;ys, n-1)))
    //(yi - (m * xi + c)) * xi
    float xi = xs->x;
    float yi = xs->y;
    float ans = (yi - (m * xi + c)) * xi;
    float rest = compute_dE_dm(xs->next, n-1, m, c); // n appears useless here
    _(fold valid_memory_inv(;xs, n))
    return (-2/n)*(ans + rest); // -2.0 is not working
    
  }     

}

float compute_dE_dc(struct list *xs, int n, float m, float c)
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
    _(assert (exists float u, float v, struct list *ys.
        &xs->x |-> u && &xs->y |-> v &&
        &xs->next |-> ys && valid_memory_inv(;ys, n-1)))
    //(yi - (m * xi + c))
    float xi = xs->x;
    float yi = xs->y;
    float ans = (yi - (m * xi + c));
    float rest = compute_dE_dc(xs->next, n-1, m, c); // n appears useless here
    _(fold valid_memory_inv(;xs, n))
    return (-2/n)*(ans + rest); // -2.0 is not working
    
  }     
}


void predict_m_and_c_using_grad_descent(struct list *xs, int n, float *m, float *c, float *learning_rate)
  _(requires valid_memory_inv(;xs, n))
  _(requires exists float lrate. learning_rate |-> lrate)
  _(requires exists float oldm. m |-> oldm)
  _(requires exists float oldc. c |-> oldc)
  _(ensures valid_memory_inv(;xs, n))
  _(ensures exists float newm. m |-> newm)
  _(ensures exists float newc. c |-> newc)
  _(ensures learning_rate |-> lrate)
  {
    /*
    Loss function is mean sum of squares
    E = 1/n \Sigma_{i = 0 to n} (yi - (m * xi + c))^2 // actual - predicted 
    dE/dm = 1/n \Sigma_{i = 0 to n} (2 * (yi - (m * xi + c)) * (-xi))
           = -2/n \Sigma_{i = 0 to n} (yi - (m * xi + c)) * xi

    dE/dc = -2/n \Sigma_{i = 0 to n} (yi - (m * xi + c))     

    m_new = m_old - Learing_rate * dE/dm 
    c_new = c_old - Learning_rant * dE/dc
    */
   float m_old = *m;
   float c_old = *c;
   float learn_rate = *learning_rate;
   float m_new;
   float c_new;
   float dm; 
   float dc;  
   int i;

   /* I am sort of calculating a fixed point
      so is there anyting I can prove interesting
      about this calculations? 
   */
  i = 0;
  while(i < 1000)
  _(invariant i :: low)
  _(invariant valid_memory_inv(;xs, n))
  {
     dm = compute_dE_dm(xs, n, m_old, c_old);
     dc = compute_dE_dc(xs, n, m_old, c_old);
     m_new = m_old - learn_rate * dm;
     m_old = m_new;
     c_new = c_old - learn_rate * dc; 
     c_old = c_new;
     i = i + 1;
  }

  *m = m_old;
  *c = c_old;
   /* So Alan's floating point implementation would 
   work because there is just one division, by n which 
   is a public value. */
  }
  

  