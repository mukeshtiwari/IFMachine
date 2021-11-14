#include "secc.h"

/* a small example inspired by Polikarpova et al.,
   "Liquid Information Flow Control", ICFP 2020. */

/* EDAS leak */

enum phases {
  PHASE_DONE,
  PHASE_NOT_DONE
};

typedef enum phases phase_t;

enum decision {
  DECISION_NONE,
  DECISION_ACCEPT,
  DECISION_REJECT
};

typedef enum decision decision_t;

/* Fixed version: Figure 4. Note the precondition says that the
   decision is low only when the phase is DONE, i.e. once the
   decision is already allowed to be made public */
void show_paper_fixed(phase_t phase, decision_t dec, int title)
  _(requires phase :: low)
  _(requires title :: low)
  _(requires phase == PHASE_DONE ==> dec :: low)
  _(ensures result :: low)
{
  int masked_dec;
  if (phase == PHASE_DONE){
    masked_dec = dec;
  }else{
    masked_dec = DECISION_NONE;
  }
  _(assert masked_dec :: low)
  if (masked_dec == DECISION_ACCEPT){
    return title+1;
  }else{
    return title;
  }
}

/* Leaky EDAS code, Figure 3. Note we model the appending of the session
   information using a simple addition. Any operation that makes the title
   distinct from its original value will do, of course */
void show_paper_insecure(phase_t phase, decision_t dec, int title)
  _(requires phase :: low)
  _(requires title :: low)
  _(requires phase == PHASE_DONE ==> dec :: low)
  _(ensures result :: low)
  _(fails insecure)
{
  if (dec == DECISION_ACCEPT){
    return title+1;
  }else{
    return title;
  }
}

