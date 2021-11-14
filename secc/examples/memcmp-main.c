#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

int memcmp_ct(int *p1, int *p2, int n);


int main(void){
  int p1[] = {5,10,20,30,40};
  int p2[] = {5,10,20,30,50};

  int r = memcmp_ct(p1,p2,4);
  if (r != 0){
    fprintf(stderr,"memcmp_ct broken! -- expected 0 got %d",r);
    exit(1);
  }

  r = memcmp_ct(p1,p2,5);
  if (r <= 0){
    fprintf(stderr,"memcmp_ct broken! -- expected positive got %d",r);
    exit(1);
  }

  printf("All OK\n");
  return 0;
}
