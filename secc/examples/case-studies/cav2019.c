struct mutex;

/* Running example from the CAV 2019 paper */
struct record { int is_classified; int data; };
struct record * rec;
int * OUTPUT_REG;

void lock(struct mutex * m);
	_(ensures exists int v.
		OUTPUT_REG |->[low()] v)
	_(ensures exists int c, int d.
		&rec->is_classified |->[low()] c &&
		&rec->data |-> d &&
		d :: (c ? high() : low()))

void unlock(struct mutex * m);
	_(requires exists int v. OUTPUT_REG |->[low()] v)
	_(requires exists int c, int d.
		&rec->is_classified |->[low()] c &&
		&rec->data |->d &&
		d :: (c ? high() : low()))

void thread1(struct mutex *mutex) {
  while(1) {
    lock(mutex);
    if(!rec->is_classified) {
      *OUTPUT_REG = rec->data;
    }
    unlock(mutex);
  }
}

void thread2(struct mutex *mutex) {
  lock(mutex);
  rec->is_classified = 0;
  rec->data = 0;
  unlock(mutex);
}

void thread1_insecure(struct mutex *mutex)
	_(fails insecure)
{
  while(1) {
    lock(mutex);
    if(rec->is_classified) { /* BUG: test is swapped */
      *OUTPUT_REG = rec->data;
    }
    unlock(mutex);
  }
}

void thread2_insecure(struct mutex *mutex)
	_(fails insecure)
{
  lock(mutex);
  rec->is_classified = 0;
  /* rec->data = 0; */  /* BUG: don't clear sensitive data */
  unlock(mutex);
}