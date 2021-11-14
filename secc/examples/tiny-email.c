/* SecC applied to the VerifyThis 2020 Long-Term Verification Challenge
 *
 * Authors: Mukesh Tiwari, Toby Murray
 */
#include "secc.h"

/* # Overview
 *
 * Our goal was to apply the SecC verifier, and in particular its support
 * for reasoning about information flow security, to model and verify one
 * part of the HAGRID case study. 
 *
 * Specifically, we chose to focus on the property that, in response to
 * requests to look up a key, that only confirmed identities associated with
 * that key should be returned.
 *
 * Our goal was to formulate this as an information flow property, requiring
 * that no information about any unconfirmed identities associated with the
 * looked-up key should be returned. Thus all unconfirmed identities should
 * be treated as confidential, and the act of confirming an identity
 * (using the associated confirmation token) effectively ``declassifies''
 * the identity, making it safe to reveal.
 *
 *
 * # The Model
 *
 * To allow us to focus on just this security policy, we decided to radically
 * simplify the model of the system. Our model below is for a system that
 * stores a single email address (and no keys at all). It supports an operation
 * to query which email address is stored. However, only once the email
 * address has been confirmed is it allowed to be revealed in response to these
 * queries.
 *
 * Registering an email address generates a confirmation token. 
 * Confirming the email address with the token declassifies it (makes it
 * classified as public and therefore allowed to be revealed). 
 * The function for looking up which email address is stored is specified
 * to return only public data.
 *
 *
 * # Secure Declassification
 *
 * We make use of SecC's support for `assume' statements to implement
 * declassification. However our model also verifies that declassification
 * only ever occurs at the correct time, i.e. that the `assume' statement
 * has not been misused.
 *
 * To do that our model records (via ghost state) a trace of events that 
 * remembers enough of the system's history to allow us to specify 
 * extensionally when declassification is allowed to occur. 
 * Specifically, it remembers the history of registration requests and what
 * confirmation tokens were issued for each request. Then when a confirmation
 * request arrives, declassification is allowed to occur only if the email
 * address and provided token matches those for the most recent registration
 * request, as recorded in the history.
 * 
 * An invariant links the runtime state of the system and the history, 
 * which is necessary to establish that declassification is safe to occur.
 */

/* SecC has very limited support for primitive types. Hence we treat email
 * addresses and tokens as ints */
typedef int email_address;
typedef int token;


/* The history of events, which is used to specify when declassification is
 * safe to occur, remembers the registration requests and what confirmation
 * tokens were generated for each request. We call these ``registration
 * events'', captured by the following type. */
struct event
{
  email_address email;
  token t;  
};
typedef struct event event_t;

/* A predicate to track the ghost state of the history of what events
 * have occurred. */
_(predicate io_trace(;list<event_t> xs))


/* this predicate captures the extensional security policy that states when
 * it is safe to declassify an email address `email' given confirmation
 * token `t'. Note that this depends only on the history of registration
 * events (i.e. it is independent of the internal state of the system).
 * Declassification can occur only when `email` was the most recently
 * registered email address and `t' matches the token that was generated
 * when `email' was registered, as recorded in the history (io_trace) */
_(predicate safe_to_declassify_email(;email_address email, token t)
  (exists event_t y, list<event_t> ys. 
   io_trace(;cons(y,ys)) && y.email == email && y.t == t))


/* The state of the system:
 * `stored_address':  which email address is currently stored,
 * `stored_token`: the confirmation token issued for that address (if any),
 * `is_confirmed': whether the address has been confirmed (0 = unconfirmed) */
struct state {
  email_address stored_address;
  token stored_token;
  int is_confirmed;
};
typedef struct state state_t;

/* This invariant that connects the state of the system to the history
 * of events stored in the io_trace. Specifically, the system state
 * should match the most recent event in the history. Additionally,
 * the stored email address is public (low) only when it's confirmed.  */
_(predicate inv(;state_t *s)
  (exists  list<event_t> ys, event_t y, email_address v, token t, int c.
   io_trace(;cons(y,ys)) &&
   y.email == v && y.t == t && 
   &s->stored_address |-> v && &s->stored_token |-> t &&
   &s->is_confirmed |-> c &&
   (c == 0 || c == 1) && c :: low &&
   c ==> v :: low))


/* An external function for generating new confirmation tokens. Its
 * specification simply updates the history to remember that the resulting
 * token was generated for the given email address */
token new_token(email_address addr);
_(requires exists list<event_t> ios. io_trace(; ios))
_(ensures exists event_t y. io_trace(; cons(y, ios)) &&
  y.email == addr && y.t == result)



/* The function that handles requests to register an email address.
 * Doing so generates a confirmation token. Its specification simply
 * ensures that the invariant above is preserved. */
token register(state_t *s, email_address addr)
  _(requires inv(;s))
  _(ensures  inv(;s))
{
  
  _(unfold inv(;s))

  s->stored_address = addr;
  token t = new_token(addr);
  s->stored_token = t;
  s->is_confirmed = 0;
  _(fold inv(;s))
  return t; 
} 


/* The function that implements requests to confirm the most recently
 * registered email address. Returns 0 on failure. Its specification
 * simply says that the invariant is preserved. */
int confirm(state_t *s, token t)
  _(requires inv(; s))
  _(ensures inv(; s))
  _(ensures result == 0 || result == 1)
{
  _(unfold inv(;s))
  int x = s->stored_token;

  /* attempting to confirm necessarily reveals whether the given token `t'
   * matches that `x' stored in the state. Hence that information must
   * be safe to release to a potential attacker, by definition.
   * The following `assume' statement captures this intuition. Formally
   * it means: ``let us assume that any attacker knows whether `t == x' '' */
  _(assume (t == x) :: low)
    
  if (t == s->stored_token){
   /* binds the logical variable v to refer to the stored address */
   _(assert exists email_address v. &s->stored_address |-> v)

   /* We explicitly check that declassification is safe to perform 
    * (by proving `safe_to_declassify_email') before
    * declassifying the stored email address (via the `assume' statement) */
   _(fold safe_to_declassify_email(; v, t))
   _(assume v :: low)
   _(unfold safe_to_declassify_email(; v, t))
     
   s->is_confirmed = 1;
   
   _(fold inv(;s)) 
   return 1; 
  }
  
  _(fold inv(;s))
  return 0;
}



/* The function that handles queries to look up the email address.
 * Its specification says that it outputs only public (low) data. 
 * Specifically, any new value placed in `p' must be low. This is what
 * ensures that it cannot reveal any information about unconfirmed addresses
 * (i.e. information has hasn't been declassified) */
int get_address(state_t *s, email_address *p)
  _(requires inv(;s))
  _(requires exists email_address vorig. p |-> vorig)
  _(ensures inv(;s))
  _(ensures exists email_address vnew. p |-> vnew)
  _(ensures (result == 1 || result == 0))
  _(ensures (result == 1) ==> (vnew :: low))
  _(ensures (result == 0) ==> (vnew == vorig))
{  
  _(unfold inv(; s))

  if (s->is_confirmed){
    *p = s->stored_address;    
  }
  
  int ret = s->is_confirmed;
  
  _(fold inv(;s))
  return ret;
}
