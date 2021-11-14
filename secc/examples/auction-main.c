#include <stdio.h> 
#include <stdlib.h> 
#include <unistd.h> 
#include <pthread.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <string.h>
#include <signal.h>

/* Secure Auction server case study.
 
  Author: Mukesh Tiwari

  This auction server is verified to ensure that the result of the auction
  is only released once the auction closes (at a fixed time set in advance)
  and never beforehand. Prior to releasing the result of the auction, no
  information about the bids received is revealed. 
  
  Importantly each connection to the server is serviced by a separate thread,
  ensuring that one client cannot block the progress of others. Hence,
  concurrency is used in this example to help make it secure. However,
  its introduction necessitates careful reasoning about information leakage
  to make sure that it doesn't reveal information during the course of the
  auction that would allow one bidder to game the system.

  To run this code:
  1. run "make auction-main" (double quotes for clarity)
  2. run "./auction-main <duration> <reserve>"
     replacing <duration> with a positive integer that defines
     the number of seconds that the auction runs for and <reserve> likewise
     with the desired reserve price. If <reserve> is omitted, no reserve
     is used.

  The auction server will listen for TCP connections on port 3000.
  Bids are of the form "<id> <quote>" where <id> and <quote> are both
  integers. e.g. one can submit a bid with id 10 and quote 20 by running:
  echo "10 20" | nc 127.0.0.1 3000 

  The shell script 'simulate-auction-clients.sh' simulates a bunch of 
  clients interacting with the server by generating a series of 
  random bids and submitting them in parallel to the server (including with 
  synthetic delays, to take advantage of the server's concurrency).

  At the conclusion of the auction, the server prints out the winning bid.
*/


#define PORT 3000                    // TCP port to listen on
#define BUFSIZE 1024                 // size of buffer for reading from socket
#define LOGFILE "trace_log.txt"

enum auction_status {
  Ready, 
  Ongoing, 
  Closed
};
typedef enum auction_status database_status;


struct id_and_quote
{
  int id;     // bidder identity
  int qt;  // bid amount
};

enum ret_code {
  Failure,
  Success
};
typedef enum ret_code status_code;

enum auc_code {
  Running, 
  Finished
};
typedef enum auc_code event_code;

struct auction_event {
  event_code acode; 
  int identity;
  int quote;
};


struct id_and_quote ts;
database_status td;
int p, q;
int reserve = 0;

extern status_code start_auction(struct id_and_quote *s, database_status *d);
extern void write_bid_in_the_database_thread(struct id_and_quote *bid);
extern void close_and_declassify_bid_thread(int delay, int *p , int *q);
extern void close_and_declassify_if_gt_resvalue(int delay, int *p, int *q, int *res);
extern struct id_and_quote *s;
extern database_status *d;


pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;

void acquire_lock(){
  pthread_mutex_lock(&g_mutex);
}

void release_lock(){
  pthread_mutex_unlock(&g_mutex);
}


struct auction_event bid_register_log(int id, int qt){
  FILE *fp = fopen(LOGFILE, "a");
  fprintf(fp, "%d %d Running\n", id, qt);
  fclose(fp);
  return (struct auction_event) {.identity = id, .quote = qt, .acode = Running };
}

struct auction_event bid_closed_log(){
  FILE *fp = fopen("trace_log.txt", "a");
  fprintf(fp, "Finished\n");
  fclose(fp);
  return (struct auction_event) {.identity = 0, .quote = 0, .acode = Finished};
}

void print_winner(int id, int quote){
  printf("The winnder is %d with winning bid %d\n", id, quote);
}

void* handle_data_to_close_and_declassify(void *arg){
  int actime = (int)arg;
  if (reserve <= 0){
    close_and_declassify_bid_thread(actime, &p, &q);
  }else{
    close_and_declassify_if_gt_resvalue(actime, &p, &q, &reserve);
  }
  return NULL;
}

void* handle_incoming_connections(void *arg){
  int connfd = (int)arg;
  char buf[BUFSIZE] = {0};
  struct id_and_quote bid;
  recv(connfd, buf, sizeof(buf), 0);
  sscanf(buf,"%d %d", &(bid.id), &(bid.qt));
  //printf("%d %d\n", bid.id, bid.qt);
  close(connfd);
  write_bid_in_the_database_thread(&bid);
  return NULL;
}


int main(int argc, char *argv[])
{
  // initialization of global variables of auction.c
  s = &ts;
  d = &td;
  
  int auction_time;
  if(argc < 2 || argc > 3){
    printf("Usage: %s <duration> [<reserve>]\n",argv[0]);
    exit(0);
  }
  auction_time = atoi(argv[1]);
  reserve = (argc == 3 ? atoi(argv[2]) : 0);

  printf("The auction duration is %d seconds; reserve: %d\n", auction_time,reserve);
  
  // start the auction
  start_auction(s, d);
  
  // server setup for 
  // accepting connections
  socklen_t clilen;
  struct sockaddr_in servaddr, cliaddr; 
  pthread_t write_thread, declassify_thread;
  int listenfd, connfd;  

  listenfd = socket(AF_INET, SOCK_STREAM, 0);
  servaddr.sin_family = AF_INET;
  servaddr.sin_addr.s_addr = htonl(INADDR_ANY);
  servaddr.sin_port = htons(PORT);
  
  if (bind(listenfd, (struct sockaddr *) &servaddr, sizeof(servaddr)) != 0){
    fprintf(stderr,"Error binding socket to port %d. Exiting.\n", PORT);
    perror(NULL);
    exit(1);
  }
  if (listen(listenfd, 8) != 0){
    fprintf(stderr,"Error listening for connections on port %d. Exiting.\n", PORT);
    perror(NULL);
    exit(1);
  }

  printf("Server is running and waiting for connections on port %d\nBids will be logged to: %s\n", PORT, LOGFILE);
  
  pthread_create(&declassify_thread, NULL, &handle_data_to_close_and_declassify, (void *)(long)auction_time);
  
  while(1){  
    clilen = sizeof(cliaddr);
    connfd = accept(listenfd, (struct sockaddr *)&cliaddr, &clilen);
    printf("Accepted connection\n");
    pthread_create(&write_thread, NULL, &handle_incoming_connections, (void *)(long)connfd); 
  }
  
  return 0;
}
