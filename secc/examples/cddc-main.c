#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/select.h>
#include <termios.h>
#include <pthread.h>

struct termios orig_termios;

#define ASCII_ESC 27
#define ASCII_LF 10
#define ASCII_CR 13
#define CTRL_C   3

const char ANSI_HIGH[] = {ASCII_ESC,'[','4','1','m','\0'};
const char ANSI_LOW[] = {ASCII_ESC,'[','4','2','m','\0'};
const char ANSI_RESET[] = {ASCII_ESC,'[','0','m','\0'};
#define SET_ANSI_HIGH (printf("%s",ANSI_HIGH))
#define SET_ANSI_LOW (printf("%s",ANSI_LOW))
#define RESET_ANSI (printf("%s",ANSI_RESET))

void reset_terminal_mode()
{
  tcsetattr(0, TCSANOW, &orig_termios);
  printf("\r\n");
}

void set_conio_terminal_mode()
{
  struct termios new_termios;

  /* take two copies - one for now, one for later */
  tcgetattr(0, &orig_termios);
  memcpy(&new_termios, &orig_termios, sizeof(new_termios));

  /* register cleanup handler, and set the new terminal mode */
  atexit(reset_terminal_mode);
  cfmakeraw(&new_termios);
  tcsetattr(0, TCSANOW, &new_termios);
}

int kbhit()
{
  struct timeval tv = { 0L, 0L };
  fd_set fds;
  FD_ZERO(&fds);
  FD_SET(0, &fds);
  return select(1, &fds, NULL, NULL, &tv);
}

int getch()
{
  int r;
  unsigned char c;
  if ((r = read(0, &c, sizeof(c))) < 0) {
    return r;
  } else {
    return c;
  }
}

typedef struct {
    int *data;        /* the backing memory */
    int capacity;     /* Probably should be a power of two but not enforced */
    int write_index;  /* intentionally not wrapped to capacity */
    int read_index;   /* intentionally not wrapped to capacity */
} rb_t;

extern rb_t * g_buf;
extern int *g_temp;
extern int SWITCH_CMD;

extern int * g_display_mode;
extern int * g_switch_mode;

extern void* output_thread(void *);
extern void* input_thread(void *);

int rb_init(rb_t *buf, int capacity, int *backing);

pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;

void lock(){
  pthread_mutex_lock(&g_mutex);
}

void unlock(){
  pthread_mutex_unlock(&g_mutex);
}

void set_colour(int mode){
  if (mode == 0){
    SET_ANSI_LOW;
  }else{
    SET_ANSI_HIGH;
  }
}
void display_mode_updated(){
  set_colour(*g_display_mode);
  printf("\r\n");

  RESET_ANSI;
  fflush(stdout);
}

int is_input_avail(){
  int c = kbhit();
  return c;
}

int get_input(){
  int c = getch();
  return c;
}

void output(int c, int mode){
  set_colour(mode);
  if (c == ASCII_LF || c == ASCII_CR){
    printf("\r\n");
  }else{
    putchar(c);
  }
  RESET_ANSI;
  fflush(stdout);
  if (c == CTRL_C){
    exit(1);
  }
}

void output_low(int c){
  output(c,0);
}
void output_high(int c){
  output(c,1);
}


rb_t g_rb;
int temp;
int dmode;
int smode;
#define BUFFER_SIZE 1024

int g_data[BUFFER_SIZE];

void random_delay(){
  struct timespec t;
  t.tv_sec = 0;
  t.tv_nsec = (long int)rand()/8;
  nanosleep(&t,NULL);
}

int main(int argc, char *argv[])
{
  if (argc != 1){
    printf("usage: %s\n",argv[0]);
    exit(1);
  }
  printf("************************************************************************\n");
  printf("                     CDDC Input Handling Simulator\n");
  printf("************************************************************************\n");  
  SWITCH_CMD = ASCII_ESC;
  printf("Type some text. Press ESC to switch modes. Low is green. High is red.\n");
  printf("Output rendering is intentionally jittery, justifying the ring buffer.\n");
  printf("\r\n");
  set_conio_terminal_mode();
  
  g_buf = &g_rb;
  memset(g_data,0,sizeof(g_data));

  g_temp = &temp;
  
  g_display_mode = &dmode;
  g_switch_mode = &smode;
  *g_display_mode = 0;
  *g_switch_mode = 0;
  display_mode_updated();
  
  rb_init(g_buf,BUFFER_SIZE,g_data);


  pthread_t input_th;
  pthread_t output_th;
  pthread_create(&input_th,NULL,&input_thread,NULL);
  pthread_create(&output_th,NULL,&output_thread,NULL);
  pthread_join(input_th,NULL);
  pthread_join(output_th,NULL);
  
}

