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
  double x;
  double y;
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

struct yvector
{
  double head;
  struct yvector *next;
};

struct gradient
{
  double m;
  double c;
  struct gradient *next;
};

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

extern void compute_yhat_from_data(double m, double c, struct private_training_data *xs, struct yvector *ys, int n);
extern void compute_gradient_m_and_c(struct yvector *yhat, struct private_training_data *xs, struct gradient *gs, int n);
extern int abs(int x);
extern void clip_gradient(struct gradient *gs, int n, double tau);
extern double sum_gradient_m(struct gradient *gs, int n);
extern double average_gradient_m(struct gradient *gs, int n);
extern double sum_gradient_c(struct gradient *gs, int n);
extern double average_gradient_c(struct gradient *gs, int n);
extern status_code start_the_client(double *budget, double eps, double refvalue);
extern status_code fill_budget(double *budget, double eps, double refvalue);
extern void recursive_gradient_descent(int k, struct  private_training_data *xs, int n, double *m, double *c, double *learning_rate, 
  double *budget, double eps, double refvalue, struct yvector *yhat, struct gradient *gs);
extern status_code predict_m_and_c_using_grad_descent(struct  private_training_data *xs, int n, double *m, double *c,
  double *mret, double *cret, double *learning_rate, double *budget, double eps, double refvalue, int k, struct yvector *yhat, struct gradient *gs);
extern status_code run_the_learning_framework();



/* 
Laplace implementation goes here.
https://www.boost.org/doc/libs/1_49_0/libs/math/doc/sf_and_dist/html/math_toolkit/dist/dist_ref/dists/laplace_dist.html
http://www.mymathlib.com/functions/probability/laplace_distribution.html
In this implementation, mu = 0 /\ sigma = 1.
f(x, mu, sigma) = 1 / (2 * sigma) * exp(-|x - mu| / sigma)
f(x,0,1) = 1 / (2 * 1) * exp(-|x| / 1)
f(x,0,1) = 0.5 * exp(-|x|)
returns a random number from a Laplace distribution with parameter tau
To get the actual predication, comment out the noise part
and just simply return 0, i.e. no noise.
*/
double laplace_noise(double x)
{
   double temp = 0.5 * exp(-fabs(x));
   return (x <= 0.0) ? temp : 1.0 - temp;
   //return 0;
}

pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;

void acquire_lock(){
  pthread_mutex_lock(&g_mutex);
}

void release_lock(){
  pthread_mutex_unlock(&g_mutex);
}

struct event add_receive_event_to_trace(double m, double c)
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

struct event add_training_event_to_trace(double *m, double *c, double *budget, double dm, 
  double dc, double eps, double learn_rate)
{

  double noise1 = laplace_noise(4 * 1.0/eps)/n;
  double noise2 = laplace_noise(4 * 1.0/eps)/n;

  double m_old = *m;
  double c_old = *c;
  double m_new; 
  double c_new;

  m_new = m_old - learn_rate * (dm + noise1);
  c_new = c_old - learn_rate * (dc + noise2);

  *m = m_new;
  *c = c_new;
  *budget = *budget - eps; 

  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Training %f %f\n", m, c);
  fclose(fp);
  return (struct event) {.est = Training, .m = m_new, .c = c_new, .m_old = m_old, 
    .dm = dm, .noise1 = noise1, .c_old = c_old, .dc = dc, .noise2 = noise2};
}

struct event add_conveyed_event_to_trace(double m, double c)
{
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "Conveyed %f %f\n", m, c);
  fclose(fp);
  return (struct event) {.est = Conveyed, .m = m, .c = c};
}


double generate_random_number() // [0, 1]
{
  return (double)rand() / (double)RAND_MAX;
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
    temp->y = temp->x; //m = 1.0, c = 0.0
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

void print_gradient(status_code t, double m, double c)
{
  printf("Trained Parameters: Status code = %d m = %f c = %f\n", t, m, c);
}


void* drive_the_learning_framework()
{
  status_code t;
  int f;
  double b;
  do 
  {
    t = run_the_learning_framework();
    b = *budget;
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
  double crime, nox;
  int i = 0;
  while(i < n)
  {
    fscanf(fp, "%lf %lf", &crime, &nox);
    xs->x = crime;
    xs->y = nox;
    xs = xs->next;
    i++;
  }
  return ts;
}





int main()
{
  
  // initialize the data structures
  double bud; // budget
  budget = &bud; // pointer to budget
  eps = 0.01; // epsilon
  refvalue = 16.0; // this is the value of the reference budget
  n = 332; // number of training data points
  k = 1000; // number of iterations

  xs = alloc_memory_xs(n); // pointer to the list of training data
  ys = alloc_memory_ys(n); // pointer to the list of yhats
  gs = alloc_memory_gs(n); // pointer to the list of gradients
  /*
  read the file crime_nox.csv and 
  write the values in xs.
  */
  // comment this line to run the algorithm on 
  // synthetic data (m = 1.0 and c = 0.0)
  // xs = read_csv_file(n);


  double tmret; 
  double cmret;
  mret = &tmret;
  cret = &cmret;
  double tm = 0.5;
  double tc = 0.5;
  m = &tm; // we start with a value of m = 0.5
  c = &tc; // we start with a value of c = 0.5
  double lrate = 0.1;
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