#include <stdio.h> 
#include <stdlib.h> 
#include <unistd.h> 
#include <pthread.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <string.h>
#include <signal.h>
#include <math.h>

/*
This is a (client) driving program that receives data, initial 
gradients, from the server. These initial values are used by 
the federated client to train the model, using differential 
privacy methods. Finally, the modified gradients are sent back
to the server. 
*/

#define PORT 3000                    // TCP port to listen on
#define BUFSIZE 1024                 // size of buffer for reading from socket
#define LOGFILE "gradient_log.txt"      // file to log the traces of computation

struct private_training_data
{
  float x;
  float y;
  struct private_training_data *next;
};

enum ev_status
{
  Received, 
  Training,
  Conveyed,
  Refilled
};
typedef enum ev_status event_status;

enum ret_code 
{
  Failure, // if a client is out of budget, it will simply return the received model parameters to server 
  Success // if a client has budge, it will train 
};
typedef enum ret_code status_code;


struct event
{
  event_status est;
  float m; 
  float c; 
  // When est == Training
  float m_old; // old m 
  float c_old; // old c 
  float dm; // averaged m 
  float dc; // averaged c
  float noise1; // noise added to m_new = m_old - learning_rate * (dm + noise1)
  float noise2; // noise added to c_new = c_old - learning_rate * (dc + noise2)
};

struct yvector
{
  float head;
  struct yvector *next;
};

struct gradient
{
  float m;
  float c;
  struct gradient *next;
};

float *budget;
float eps; 
float refvalue;
struct  private_training_data *xs;
struct yvector *ys;
struct gradient *gs;
int n;
float *m;
float *c;
float *mret; 
float *cret;
float *learning_rate;
int k;

extern void compute_yhat_from_data(float m, float c, struct private_training_data *xs, struct yvector *ys, int n);
extern void compute_gradient_m_and_c(struct yvector *yhat, struct private_training_data *xs, struct gradient *gs, int n);
extern int abs(int x);
extern void clip_gradient(struct gradient *gs, int n, float tau);
extern float sum_gradient_m(struct gradient *gs, int n);
extern float average_gradient_m(struct gradient *gs, int n);
extern float sum_gradient_c(struct gradient *gs, int n);
extern float average_gradient_c(struct gradient *gs, int n);
extern status_code start_the_client(float *budget, float eps, float refvalue);
extern status_code fill_budget(float *budget, float eps, float refvalue);
extern void recursive_gradient_descent(int k, struct  private_training_data *xs, int n, float *m, float *c, float *learning_rate, 
  float *budget, float eps, float refvalue, struct yvector *yhat, struct gradient *gs);
extern status_code predict_m_and_c_using_grad_descent(struct  private_training_data *xs, int n, float *m, float *c,
  float *mret, float *cret, float *learning_rate, float *budget, float eps, float refvalue, int k, struct yvector *yhat, struct gradient *gs);
extern status_code run_the_learning_framework();



// Laplace implementation goes here.
// https://www.boost.org/doc/libs/1_49_0/libs/math/doc/sf_and_dist/html/math_toolkit/dist/dist_ref/dists/laplace_dist.html
// http://www.mymathlib.com/functions/probability/laplace_distribution.html
// In this implementation, mu = 0 /\ sigma = 1.
// f(x, mu, sigma) = 1 / (2 * sigma) * exp(-|x - mu| / sigma)
// f(x,0,1) = 1 / (2 * 1) * exp(-|x| / 1)
// f(x,0,1) = 0.5 * exp(-|x|)
// returns a random number from a Laplace distribution with parameter tau
// To get the actual predication, comment out the noise part
// and just simply return 0, i.e. no noise.
float laplace_noise(float x)
{
   float temp = 0.5 * exp(-fabs(x));
   //printf("x and laplace_noise:%f %f\n", x, temp);
   //return (x <= 0.0) ? temp : 1.0 - temp;
   return 0; // disregard any differential privacy (this is for testing because we return no noise)
}

pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;

void acquire_lock(){
  pthread_mutex_lock(&g_mutex);
}

void release_lock(){
  pthread_mutex_unlock(&g_mutex);
}

struct event add_receive_event_to_trace(float m, float c)
{
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Received %f %f\n", m, c);
  fclose(fp);
  return (struct event) {.est = Received, .m = m, .c = c};
}

struct event add_refill_event_to_trace()
{
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Budget Refilled\n");
  fclose(fp);
  return (struct event) {.est = Refilled};
}

struct event add_training_event_to_trace(float m_new, float m_old, float dm,
  float noise1, float c_new, float c_old, float dc, float noise2, float learning_rate)
{
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Training %f %f\n", m, c);
  fclose(fp);
  return (struct event) {.est = Training, .m = m_new, .c = c_new, .m_old = m_old, 
    .dm = dm, .noise1 = noise1, .c_old = c_old, .dc = dc, .noise2 = noise2};
}

struct event add_conveyed_event_to_trace(float m, float c)
{
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Conveyed %f %f\n", m, c);
  fclose(fp);
  return (struct event) {.est = Conveyed, .m = m, .c = c};
}


float generate_random_number() // [0, 1]
{
  return (float)rand() / (float)RAND_MAX;
}


// Synthetic data generation (https://github.com/anonymous-conf/dplr/blob/master/code/example.py#L12)
// allocated memory and data according to 
// the equation y = 1.0 * x + 0.0
struct private_training_data *alloc_memory_xs(int n)
{
  if(n == 0)
    return NULL;
  else 
  {
    struct private_training_data *temp = (struct private_training_data *)malloc(sizeof(struct private_training_data));
    temp->x = generate_random_number();
    temp->y = 0.5 * temp->x + 0.5 ; //m = 0.5, c = 0.5 but change this to anything and see the prediction
    temp->next = alloc_memory_xs(n-1);
    return temp;
  }
}

//allocates memory for ys
struct yvector *alloc_memory_ys(int n)
{
  if(n == 0)
    return NULL;
  else
  {
    struct yvector *temp = (struct yvector *)malloc(sizeof(struct yvector));
    temp->next = alloc_memory_ys(n-1);
    return temp;
  }
}

//allocates memory for gs
struct gradient *alloc_memory_gs(int n)
{
  if(n == 0)
    return NULL;
  else
  {
    struct gradient *temp = (struct gradient *)malloc(sizeof(struct gradient));
    temp->next = alloc_memory_gs(n-1);
    return temp;
  }
}

void print_gradient(status_code t, float m, float c)
{
  printf("Trained Parameters: Status code = %d m = %f c = %f\n", t, m, c);
}


void* drive_the_learning_framework()
{
  status_code t;
  int f;
  float b;
  do 
  {
    t = run_the_learning_framework();
    b = *budget;
    // f = (fabs(b) <= 1e-6);
  } while(t);
  
  return 0;
}

// read the csv file
struct private_training_data *read_csv_file(int n)
{
  FILE *fp;
  fp = fopen("examples/federated_learning/crime_nox.csv", "r");
  if(fp == NULL) {
    printf("file can't be read\n");
    exit(0);
  }
  // skip the first line of the file
  // because it's a string
  fscanf(fp, "%*[^\n]\n");

  struct private_training_data *ts;
  ts = xs;
  float crime, nox;
  int i = 0;
  while(i < n)
  {
    fscanf(fp, "%f %f", &crime, &nox);
    xs->x = nox;
    xs->y = crime;
    xs = xs->next;
    i++;
  }
  return ts;
}


/*

Notes: This program works excellent, almost predict the  m = 0.999677 c = 0.000208 for 
the artificially generated data xs = alloc_memory_xs(n) (with m = 1.0 and c = 0.0)
if I don't add any noise, i.e., return 0 from laplace_noise. Also, make 
refvalue = 16,000 to have more iterations and comment the 
sleep function, in the last function,  in client_fed_learn.c.

*/


int main()
{
  
  // initialize the data structures
  float bud; // budget
  budget = &bud; // pointer to budget
  eps = 0.1; // epsilon
  refvalue = 1600000.0; // this is the value of the reference budget
  n = 332; // number of training data points
  k = 10; // number of iterations

  xs = alloc_memory_xs(n); // pointer to the list of training data
  ys = alloc_memory_ys(n); // pointer to the list of yhats
  gs = alloc_memory_gs(n); // pointer to the list of gradients
  /*
  read the file crime_nox.csv and 
  write the values in xs.
  */
  xs = alloc_memory_xs(n); //artifically generated data so go the function and change m and c and run this code see the prediction  

  //xs = read_csv_file(n); 

  float tmret; 
  float cmret;
  mret = &tmret;
  cret = &cmret;
  float tm = 0.5;
  float tc = 0.5;
  m = &tm; // we start with a value of m = 0.5
  c = &tc; // we start with a value of c = 0.5
  float lrate = 0.1;
  learning_rate = &lrate;

  // start the client
  start_the_client(budget, eps, refvalue);

  // add buget for learning, just once
  fill_budget(budget, eps, refvalue);

  // This thread would keep the learning process going, until the budget is finished.
  pthread_t learning_thread;
  pthread_create(&learning_thread, NULL, &drive_the_learning_framework, NULL);
  pthread_join(learning_thread, NULL);
  return 0;

}


/*
For crime_nox.csv dataset, the value of m = 0.142956 and c = 0.134787 before 
the budget finishes. 

(base) ➜  secc git:(differential-privacy-machine-learning) ✗ ./client-fed-main
Trained Parameters: Status code = 1 m = 0.109636 c = 0.109384
Trained Parameters: Status code = 1 m = 0.132323 c = 0.131565
Trained Parameters: Status code = 1 m = 0.137231 c = 0.135915
Trained Parameters: Status code = 1 m = 0.138531 c = 0.136646
Trained Parameters: Status code = 1 m = 0.139098 c = 0.136643
Trained Parameters: Status code = 1 m = 0.139517 c = 0.136491
Trained Parameters: Status code = 1 m = 0.139905 c = 0.136308
Trained Parameters: Status code = 1 m = 0.140288 c = 0.136119
Trained Parameters: Status code = 1 m = 0.140669 c = 0.135929
Trained Parameters: Status code = 1 m = 0.141050 c = 0.135739
Trained Parameters: Status code = 1 m = 0.141431 c = 0.135549
Trained Parameters: Status code = 1 m = 0.141812 c = 0.135358
Trained Parameters: Status code = 1 m = 0.142194 c = 0.135168
Trained Parameters: Status code = 1 m = 0.142575 c = 0.134977
Trained Parameters: Status code = 1 m = 0.142956 c = 0.134787
Trained Parameters: Status code = 0 m = 0.142956 c = 0.134787
Trained Parameters: Status code = 0 m = 0.142956 c = 0.134787
*/
