#include "secc.h"

enum auction_status
{
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


enum ret_code 
{
  Failure,
  Success
};
typedef enum ret_code status_code;

enum auc_code
{
  Running, 
  Finished
};
typedef enum auc_code event_code;

struct auction_event
{
  event_code acode; 
  int identity;
  int quote;
};

// logical packing fuction and axiom about its behaviour
_(function struct id_and_quote abs_pack(int id, int qt))
_(axioms
  forall int id, int qt. abs_pack(id, qt).qt == qt;
  forall int id, int qt. abs_pack(id, qt).id == id;
  forall struct id_and_quote a. abs_pack(a.id, a.qt) == a)


// maximum of two structs and axiom about its behaviour
_(function struct id_and_quote abs_max(struct id_and_quote a, struct id_and_quote b))
_(rewrites
    forall struct id_and_quote a, struct id_and_quote b. 
     a.qt >= b.qt ==> abs_max(a, b) == a;
    forall struct id_and_quote a, struct id_and_quote b. 
     a.qt < b.qt ==> abs_max(a, b) == b)


#if __SECCC 

void abs_max_gteq_proof(struct id_and_quote a, struct id_and_quote b)
 _(requires a.qt >= b.qt)
 _(ensures abs_max(a, b) == a)
 _(lemma) _(pure)
 {
   return;
 }    

void abs_max_lt_proof(struct id_and_quote a, struct id_and_quote b)
 _(requires a.qt < b.qt)
 _(ensures abs_max(a, b) == b)
 _(lemma) _(pure)
 {
   return;
 }   

#endif

_(predicate io_trace(;list<struct auction_event> xs))

 /* e is the maximum bid auction_event and ios is list of Running traces so far  */   
_(function bool max_auction_trace(struct auction_event e, list<struct auction_event> ios))
_(rewrites 
    forall struct auction_event e. max_auction_trace(e, nil) <=> true; 
    forall struct auction_event e, struct auction_event x, 
      list<struct auction_event> xs. max_auction_trace(e, cons(x, xs)) <=>
        (x.acode == Running && e.quote >= x.quote && max_auction_trace(e, xs)))  


_(function struct auction_event abs_max_event(struct auction_event e, struct auction_event st))
_(rewrites 
    forall struct auction_event e, struct auction_event st. 
      e.quote >= st.quote ==> abs_max_event(e, st) == e;
    forall struct auction_event e, struct auction_event st. 
      e.quote < st.quote ==> abs_max_event(e, st) == st)
    
#if __SECC

void abs_max_event_proof(struct auction_event e, struct auction_event st)
_(ensures (abs_max_event(e, st) == e || abs_max_event(e, st) == st) &&
      (abs_max_event(e, st).quote >= e.quote) && 
      (abs_max_event(e, st).quote >= st.quote))
_(lemma) _(pure)
{
    _(assert exists int eqt. e.quote == eqt)
    _(assert exists int sqt. st.quote == sqt)
    if(eqt >= sqt)
    {
      _(assert e.quote >= st.quote)
    }
    else
    {
      _(assert e.quote < st.quote)
    }     
}

#endif

// boolean predicate that tests if st is member of list ios 
_(function bool member(struct auction_event st, list<struct auction_event> ios))
_(rewrites 
      forall struct auction_event st. member(st, nil) <=> false;
      forall struct auction_event st, struct auction_event x, 
        list<struct auction_event> xs. ((member(st, cons(x, xs))) <=> 
         (st == x ||  member(st, xs))))


_(predicate auction_database_inv(struct id_and_quote *s,  database_status *d; list<struct auction_event> ios)
  (exists int id, int qt, database_status alpha.
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed) &&
    ((alpha == Ready) ==> (ios == nil)) &&
    ((alpha == Ongoing) ==>  
      (exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))) &&
    ((alpha == Closed) ==> 
      (exists struct auction_event st, struct auction_event x,
        list<struct auction_event> xs.  
        ios == cons(x, xs) &&
        x.acode == Finished &&
        (member(st, xs) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, xs) <=> true)))))



_(predicate safe_to_declassify_bid(int id, int qt, list<struct auction_event> ios)
   (exists struct auction_event x, list<struct auction_event> xs, 
    struct auction_event st. io_trace(;ios) &&
    ios == cons(x, xs) && x.acode == Finished &&
    (member(st, xs) <=> true) &&
    st.acode == Running && st.quote == qt && st.identity == id &&
    (max_auction_trace(st, xs) <=> true)))


_(function bool no_finished_in_trace(list<struct auction_event> ios))
_(rewrites 
    no_finished_in_trace(nil) <=> true;
    forall struct auction_event x, list<struct auction_event> xs. 
      (no_finished_in_trace(cons(x, xs)) <=> 
      (x.acode == Running && no_finished_in_trace(xs))))


struct auction_event bid_register_log(int id, int qt);
_(requires exists list<struct auction_event> ios. io_trace(; ios))
_(requires no_finished_in_trace(ios) <=> true) 
_(ensures io_trace(;cons(result, ios)) &&
  result.acode == Running && result.identity == id && result.quote == qt)



struct auction_event bid_closed_log();
_(requires exists list<struct auction_event> ios. io_trace(; ios))
_(requires no_finished_in_trace(ios) <=> true)
_(ensures exists struct auction_event e. io_trace(;cons(e, ios)) &&
  e.acode == Finished)

#if __SECC

void max_trace_auction_has_no_finished(struct auction_event st, list<struct auction_event> ios)
_(requires exists int id, int qt. st.acode == Running && st.identity == id && st.quote == qt)
_(requires max_auction_trace(st, ios) <=> true)
_(ensures no_finished_in_trace(ios) <=> true)
_(lemma) _(pure)
{
  if (ios != nil)
  {
    _(assert exists struct auction_event x, list<struct auction_event> xs. ios == cons(x, xs))
    _(assert max_auction_trace(st, cons(x, xs)) <=>
        (x.acode == Running && st.quote >= x.quote && max_auction_trace(st, xs)))
    max_trace_auction_has_no_finished(st, xs);    
  }
  
}

void no_finished_trace_in_start_or_ongoing_state(struct id_and_quote *s, database_status *d, list<struct auction_event> ios, int id, int qt, database_status alpha)
_(requires
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed) &&
    ((alpha == Ready) ==> (ios == nil)) &&
    ((alpha == Ongoing) ==>  
      (exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))))
 _(requires alpha == Ready || alpha == Ongoing)
 _(ensures no_finished_in_trace(ios) <=> true)
 _(ensures &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed) &&
    ((alpha == Ready) ==> (ios == nil)) &&
    ((alpha == Ongoing) ==>  
      (exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))))
 _(lemma)
 {
  if(alpha == Ongoing)
   {
     _(assert exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))
     _(apply max_trace_auction_has_no_finished(st, ios);) 
     return;

   }
 }
#endif 


// Make the database ready for auction 
status_code start_auction(struct id_and_quote *s, database_status *d)
_(requires io_trace(;nil))
_(requires exists int id. &s->id |-> id)
_(requires exists int qt. &s->qt |-> qt)
_(requires exists database_status alpha. d |-> alpha)
_(ensures result == Success)
_(ensures auction_database_inv(s, d; nil))
_(ensures io_trace(;nil))
{
  *d = Ready;
  _(fold auction_database_inv(s, d; nil))
  return Success;
} 

#if __SECC

void ios_membership_tail(struct auction_event e, struct auction_event st, list<struct auction_event> ios)
_(requires member(st, ios) <=> true)
_(ensures member(st, cons(e, ios)) <=> true)
_(lemma) _(pure)
{
  return;
}

void ios_membership_head(struct auction_event e, struct auction_event st, list<struct auction_event> ios)
_(ensures member(e, cons(e, ios)) <=> true)
_(lemma) _(pure)
{
  return;
}

void max_event_membership_proof(struct auction_event est, struct auction_event e, struct auction_event st, 
    list<struct auction_event> ios)
_(requires est == abs_max_event(st, e))
_(requires member(e, cons(e, ios)) <=> true)
_(requires member(st, ios) <=> true)
_(ensures member(est, cons(e, ios)) <=> true)
_(lemma) _(pure)
{
  
  abs_max_event_proof(st, e);
}



void max_auction_trace_helper_proof(struct auction_event e, struct auction_event st, list<struct auction_event> ios)
_(requires e.quote >= st.quote)
_(requires max_auction_trace(st, ios) <=> true)
_(ensures max_auction_trace(e, ios) <=> true)
_(lemma) _(pure)
{
  if(ios != nil)
  {
    _(assert exists struct auction_event x, list<struct auction_event> xs. ios == cons(x, xs))
    _(assert max_auction_trace(st, cons(x, xs)) <=> 
          (x.acode == Running && st.quote >= x.quote &&
            max_auction_trace(st, xs)))
    max_auction_trace_helper_proof(e, st, xs);
  }
}


void max_auction_trace_wellfounded(struct auction_event est, struct auction_event e, struct auction_event st, 
    list<struct auction_event> ios, list<struct auction_event> iost)
_(requires e.acode == Running)    
_(requires est == abs_max_event(st, e))
_(requires iost == cons(e, ios))
_(requires max_auction_trace(st, ios) <=> true)
_(ensures max_auction_trace(est, iost) <=> true)
_(pure) _(lemma)
{
   abs_max_event_proof(st, e);
  
  if (est != st)
    max_auction_trace_helper_proof(e, st, ios);
}


void case_analysis_on_events(int eid, int eqt, struct auction_event e,
                             int stid, int stqt, struct auction_event st,
                             struct auction_event est, 
                             int mxqt, int mxid)
  _(requires mxqt == abs_max(abs_pack(stid, stqt), abs_pack(eid, eqt)).qt)
  _(requires mxid == abs_max(abs_pack(stid, stqt), abs_pack(eid, eqt)).id)  
  _(requires st.acode == Running && st.identity == stid && st.quote == stqt)
  _(requires e.acode == Running && e.identity == eid && e.quote == eqt)
  _(requires est == abs_max_event(st, e))
  _(ensures est.acode == Running && est.identity == mxid && est.quote == mxqt)
  _(lemma) _(pure)
{
    _(apply abs_max_event_proof(st, e);)
    _(assert exists struct id_and_quote stp. stp == abs_pack(stid,stqt))
    _(assert exists struct id_and_quote ep.  ep == abs_pack(eid,eqt))      
    if(stqt >= eqt)
    {
      abs_max_gteq_proof(stp,ep);
      _(assert st.quote >= e.quote)
      _(assert abs_max_event(st, e) == st)
      _(assert mxid == stid)
    }
    else
    {
      abs_max_lt_proof(stp,ep);
      _(assert abs_max_event(st, e) == e)
      _(assert mxid == eid)        
    }
}
  

void fold_auction_database_inv_proof(struct id_and_quote *s, database_status *d, struct auction_event est, int mxid, int mxqt,  database_status alpha, list<struct auction_event> iost)
 _(requires &s->id |-> mxid)
 _(requires &s->qt |-> mxqt)
 _(requires d |-> alpha)
 _(requires alpha == Ongoing)
 _(requires member(est, iost) <=> true)
 _(requires est.acode == Running && est.identity == mxid && est.quote == mxqt)
 _(requires max_auction_trace(est, iost) <=> true)
 _(ensures auction_database_inv(s, d; iost))
 _(lemma)
 {
   _(fold auction_database_inv(s, d; iost))
   return;
 }


_(function int abs_to_int(bool b))
_(rewrites
    abs_to_int(false) == 0;
    abs_to_int(true) == 1)

void abs_to_int_lt_proof(int aqt, int bqt, int t)
_(requires aqt < bqt)
_(requires t == abs_to_int(aqt >= bqt))
_(ensures t == 0)
_(lemma) _(pure)
{
  if (aqt < bqt)
  {
    _(assert abs_to_int(false) == 0)
  }
  
}

void abs_to_int_gt_proof(int aqt, int bqt, int t)
_(requires aqt >= bqt)
_(requires t == abs_to_int(aqt >= bqt))
_(ensures t == 1)
_(lemma) _(pure)
{

  if(aqt >= bqt)
  {
    _(assert abs_to_int(true) == 1)
  }
  
}

#endif

#if __SECC
int to_int(bool b);
  _(ensures result == abs_to_int(b))
#else
#define to_int(x)  (x)
#endif

#if __SECC

void max_struct_proof(int aid, int aqt, int bid, int bqt, int t, int rid, int rqt)
_(requires t == abs_to_int(aqt >= bqt))
_(requires rid == t * aid + (1 - t) * bid)
_(requires rqt == t * aqt + (1 - t) * bqt)
_(ensures rid == abs_max(abs_pack(aid, aqt), abs_pack(bid, bqt)).id)
_(ensures rqt == abs_max(abs_pack(aid, aqt), abs_pack(bid, bqt)).qt)
_(lemma) _(pure)
{

  if (aqt >= bqt)
  {
    _(apply abs_to_int_gt_proof(aqt, bqt, t);)
    _(assert t == 1)
    _(assert exists struct id_and_quote a. a == abs_pack(aid, aqt))
    _(assert exists struct id_and_quote b. b == abs_pack(bid, bqt))
    _(apply abs_max_gteq_proof(a, b);)
    return;
  }
  else
  {
    _(assert aqt < bqt)
     _(apply abs_to_int_lt_proof(aqt, bqt, t);)
    _(assert t == 0)
    _(assert exists struct id_and_quote a. a == abs_pack(aid, aqt))
    _(assert exists struct id_and_quote b. b == abs_pack(bid, bqt))
    _(apply abs_max_lt_proof(a, b);)
    return; 
  }
}

#endif

void inplace_maximum_of_two_structs(struct id_and_quote *a, struct id_and_quote *b)
_(requires exists int _aid, int _aqt. &a->id |-> _aid && &a->qt |-> _aqt)
_(requires exists int _bid, int _bqt. &b->id |-> _bid && &b->qt |-> _bqt)
_(ensures exists int _anid, int _anqt. &a->id |-> _anid && &a->qt |-> _anqt)
_(ensures &b->id |-> _bid && &b->qt |-> _bqt)
_(ensures _anid == abs_max(abs_pack(_aid,_aqt), abs_pack(_bid,_bqt)).id)
_(ensures _anqt == abs_max(abs_pack(_aid,_aqt), abs_pack(_bid,_bqt)).qt)
{

  int aid = a->id;
  int aqt = a->qt;
  int bid = b->id;
  int bqt = b->qt;
  
  int t = to_int(aqt >= bqt);
  int rid = t * aid + (1 - t) * bid; 
  int rqt = t * aqt + (1 - t) * bqt;
  _(apply max_struct_proof(aid, aqt, bid, bqt, t, rid, rqt);)
  a->id = rid; 
  a->qt = rqt;
  return;
}

status_code register_bid(struct id_and_quote *s, database_status *d, struct id_and_quote *bid)
_(requires exists list<struct auction_event> ios. io_trace(;ios))
_(requires auction_database_inv(s, d; ios))
_(ensures result :: low)
_(requires exists int bidid, int bidqt. &bid->id |-> bidid && &bid->qt |-> bidqt)
_(ensures &bid->id |-> bidid && &bid->qt |-> bidqt)
_(ensures exists list<struct auction_event> iost. io_trace(; iost))
_(ensures result == Success ==> exists struct auction_event e. 
      e.acode == Running && e.identity == bidid && e.quote == bidqt &&
      iost == cons(e, ios))
_(ensures result == Failure ==> iost == ios)
_(ensures auction_database_inv(s, d; iost))
{
  _(unfold auction_database_inv(s, d; ios))
  _(assert exists int id, int qt, database_status alpha.
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed))

    database_status stp = *d;
    if (stp == Closed)
    {
      
      // The auction is closed so do nothing
      _(fold auction_database_inv(s, d; ios))
      return Failure;
    }
    else if(stp == Ready)
    {
      _(apply no_finished_trace_in_start_or_ongoing_state(s, d, ios, id, qt, alpha);)

      s->id = bid->id;
      s->qt = bid->qt;
      *d = Ongoing;

      struct auction_event e = bid_register_log(bid->id, bid->qt);
      _(fold auction_database_inv(s, d; cons(e, ios)))
      return Success;    
    }
    else
    {
      _(assert stp == Ongoing)
      _(assert exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))
      _(apply no_finished_trace_in_start_or_ongoing_state(s, d, ios, id, qt, alpha);)

      struct auction_event e = bid_register_log(bid->id, bid->qt);
      inplace_maximum_of_two_structs(s, bid);
        
      _(assert exists list<struct auction_event> iost. iost == cons(e, ios) && io_trace(;iost))        
      _(assert exists struct auction_event est. est == abs_max_event(st, e))
      _(apply abs_max_event_proof(st, e);)
      _(apply ios_membership_tail(e, st, ios);)
      _(apply ios_membership_head(e, st, ios);)
      _(apply max_event_membership_proof(est, e, st, ios);)
      _(apply max_auction_trace_wellfounded(est, e, st, ios, iost);)
      _(apply case_analysis_on_events(bidid, bidqt, e, id, qt, st, est, s->qt, s->id);)
      _(apply fold_auction_database_inv_proof(s, d, est, s->id, s->qt, alpha, iost);)
      return Success;
    }   
}




status_code close_auction_and_declassify(struct id_and_quote *s, database_status *d, int *p, int *q) 
_(requires exists list<struct auction_event> ios. io_trace(;ios))
_(requires auction_database_inv(s, d; ios))
_(requires exists int opval. p |-> opval)
_(requires exists int oqval. q |-> oqval)
_(ensures result :: low)
_(ensures result == Success || result == Failure)
_(ensures exists list<struct auction_event> iost. io_trace(; iost))
_(ensures result == Success ==> exists struct auction_event e. 
      e.acode == Finished && iost == cons(e, ios))
_(ensures result == Success ==> exists int npval. p |-> npval && npval :: low) 
_(ensures result == Success ==> exists int nqval. q |-> nqval && nqval :: low)       
_(ensures result == Failure ==> iost == ios) 
_(ensures result == Failure ==> p |-> opval)
_(ensures result == Failure ==> q |-> oqval)
_(ensures auction_database_inv(s, d; iost))
{

  _(unfold auction_database_inv(s, d; ios))
  _(assert exists int id, int qt, database_status alpha.
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed))

    database_status stp = *d;
    if(stp == Ready)
    {
      // The auction has not started yet 
      // so there is no point of closing it
      _(fold auction_database_inv(s, d; ios))
      return Failure;

    }
    else if (stp == Closed)
    {
      // The auction is closed so there is 
      // no point of closing it again
      _(fold auction_database_inv(s, d; ios))
      return Failure;
    }
    else
    {
      _(assert exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))
      _(apply no_finished_trace_in_start_or_ongoing_state(s, d, ios, id, qt, alpha);)
      *d = Closed;
      *p = s->id;
      *q = s->qt;

      
      struct auction_event e = bid_closed_log();
      _(assert exists struct auction_event e. io_trace(;cons(e, ios)) &&
          e.acode == Finished)
      _(assert exists list<struct auction_event> iost. iost == cons(e, ios) && 
          io_trace(;iost))
      
      
      _(assert iost == cons(e, ios) &&
          e.acode == Finished &&
          (member(st, ios) <=> true) &&
          st.acode == Running && st.identity == id && st.quote == qt &&
          (max_auction_trace(st, ios) <=> true)) 


       _(fold safe_to_declassify_bid(id, qt, iost))
       _(assume id :: low) // safely declassify the id
       _(assume qt :: low) // safely declassify the bid
       _(unfold safe_to_declassify_bid(id, qt, iost))   
       _(fold auction_database_inv(s, d; iost))
       return Success;
      
    }
}



/* 
This function will check if the winning bid computed in the close_aution_bid is greater 
than the reserve bid set by auctioneer. If so, winner is declared (success) and declassify 
the bid and the corresponding identity. Notice that  here we have a different predicate 
for declassifcation predicate, safe_to_declassify_reserve_met, which ensures that 
the winning bid is greater than or equal to the reserve value. Otherwise, 
we return failure (and no declassification). One of key point of our formalisation 
is that many declassification policies, depending on the requirement of data declassication, 
can be pluged. We call it policy agnostic, i.e. policy is entangled with implimentation. 


This reserve will be set in the beginning of auction, and it does 
not change during the auction period.
*/ 


/* reserve predicate */
_(predicate reserve_predicate(;int reserve))

/*

The advantage of keeping the declassification decoupled from the main code is that 
a programmer can extend the source code and write her own declassifcation predicate 
without modifying any existing ones. Furthermore, she can use these predicates to 
compose a new predicate (see below). An auditor needs to check these predicates
and see if it captures the true intention. In this case, we are declassifying a bit, met, 
for further declassification (composition). The bit, met, is 1 when the winning bid, a high
value at this point,is more than the supporting price, reserve, a high value. 
At this point, both, the winning bid and resalue are high, so to take decision that 
if resvalue is greater than the winning bid or not, we cannot use if else condtion and 
we use constant time function, is_first_gt_second, to calculate which one is bigger. 
We declassify met, and if met is 1, we declassify the winning bid and the corresponding 
idenity, otherwise we do nothing (no declassification of bid and identity). 

*/

_(predicate safe_to_release_bit(;int met, int reserve, struct auction_event x, list<struct auction_event> xs, 
  list<struct auction_event> ios)
    (ios == cons(x, xs)) &&
    (io_trace(;ios)) &&
    (x.acode == Finished) &&
    (reserve_predicate(;reserve)) &&
    (met == 0 || met == 1) &&  // met is either 0 or 1
    (met == exists_a_bid_gt_than_reserve(reserve, xs)))

/* 
Compositional policy design. In this policy, we ensure that the winning bid quantity is more than the value, reserve, 
set by the auctioneer. A programmer is free to write her own policy or reuse the already defined one. Likewise, 
we can come up with many conditions on winning bid, but we do not need to touch any existing code! 
*/ 

_(predicate safe_to_declassify_when_reserve_met(;int met, int reserve, int id, int qt, list<struct auction_event> ios)
    (reserve_predicate(;reserve)) && // reserve is the minimum supporting price of an auction
    (met :: low) && // met is low
    (met == 0 || met == 1) &&  // met is either 0 or 1 
    ((met == 1) == (qt >= reserve)) &&
    (met == exists_a_bid_gt_than_reserve(reserve, ios)) && // return 1 when there is at least one bid in ios which is greater than reserve, otherwise 0
    (qt >= reserve) && 
    safe_to_declassify_bid(id, qt, ios)) // plug safe to declassify policy. 


_(function int exists_a_bid_gt_than_reserve(int reserve, list<struct auction_event> ios))
_(rewrites 
    forall int res. exists_a_bid_gt_than_reserve(res, nil) == 0; 
    forall int res, struct auction_event x, 
      list<struct auction_event> xs. exists_a_bid_gt_than_reserve(res, cons(x, xs)) == 
        ((x.quote >= res) ? 1 : (exists_a_bid_gt_than_reserve(res, xs))))



#if __SECC


void exists_reserve_0_1(int res, list<struct auction_event> ios)
_(ensures exists_a_bid_gt_than_reserve(res, ios) == 0 ||
          exists_a_bid_gt_than_reserve(res, ios) == 1)
_(lemma) _(pure)
{
  if(ios == nil)
  {
    _(assert exists_a_bid_gt_than_reserve(res, nil) == 0)
    return;
  }
  else
  {
    _(assert exists struct auction_event x, list<struct auction_event> xs. cons(x, xs) == ios)
    _(assert exists int xqt. xqt == x.quote)
    if (xqt >= res)
    {
      _(assert exists_a_bid_gt_than_reserve(res, cons(x, xs)) == 1)
      return;
    }
    else
    {
      _(assert exists_a_bid_gt_than_reserve(res, cons(x, xs)) == (exists_a_bid_gt_than_reserve(res, xs)))
      exists_reserve_0_1(res, xs);
      return;
    }
    
  }

}

void max_auction_true_case(struct auction_event st, struct auction_event y, list<struct auction_event> ys, list<struct auction_event> ios)
_(requires ios == cons(y, ys))
_(requires max_auction_trace(st, ios) <=> true)
_(ensures max_auction_trace(st, ys) <=> true)
_(lemma) _(pure)
{

  if (ios == nil)
  {
    _(assert nil == cons(y, ys))
    _(assert false)
  }
  else
  {
    _(assert exists struct auction_event x, list<struct auction_event> xs. ios == cons(x, xs))
    _(assert cons(x, xs) == cons(y, ys))
    _(assert x == y)
    _(assert xs == ys)
    _(assert max_auction_trace(st, cons(x, xs)) <=>
        (x.acode == Running && st.quote >= x.quote && max_auction_trace(st, xs)))
    _(assert (true <=> (x.acode == Running && st.quote >= x.quote && max_auction_trace(st, xs))))
    _(assert max_auction_trace(st, xs) <=> true)
    
  }
  
}


void exists_bid_equal_met_true_case(int sid, int sqt, int resvalue, struct auction_event st, list<struct auction_event> xs)
_(requires sqt >= resvalue)
_(requires (member(st, xs) <=> true))
_(requires (max_auction_trace(st, xs) <=> true))
_(requires st.acode == Running && st.identity == sid && st.quote == sqt)
_(ensures exists_a_bid_gt_than_reserve(resvalue, xs) == 1)
_(lemma) _(pure)
{
  if(xs == nil)
  {
    _(assert (member(st, nil) <=> false))
    _(assert false)
  }
  else
  {
    _(assert exists struct auction_event y, list<struct auction_event> ys. cons(y, ys) == xs)
    if(y == st)
    {
      _(assert exists int yid. yid == y.identity)
      _(assert exists int yqt. yqt == y.quote)
      _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 
           ((y.quote >= resvalue) ? 1 : (exists_a_bid_gt_than_reserve(resvalue, ys))))
      _(assert yqt == sqt)
      _(assert yqt >= resvalue)
      _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 1)

    }
    else
    {
     _(assert y != st)
     _(assert exists int yid. yid == y.identity)
     _(assert exists int yqt. yqt == y.quote)
     _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 
           ((y.quote >= resvalue) ? 1 : (exists_a_bid_gt_than_reserve(resvalue, ys))))

     _(assert ((member(st, cons(y, ys))) <=> (st == y ||  member(st, ys))))
     _(assert (member(st, ys)) <=> true)
     _(apply max_auction_true_case(st, y, ys, xs);)
     _(assert max_auction_trace(st, ys) <=> true)
     // This quote could also be greater than resvalue, but not the winning quote
     if (yqt >= resvalue)
     {
       _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 1)
     }      
     else
     {
       //Inductive case
       _(assert yqt < resvalue)
       _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == (exists_a_bid_gt_than_reserve(resvalue, ys)))
       exists_bid_equal_met_true_case(sid, sqt, resvalue, st, ys);
       
     }

    }
    
  }

}

void exists_bid_equal_met_false_case(int sid, int sqt, int resvalue, struct auction_event st, list<struct auction_event> xs)
_(requires sqt < resvalue)
_(requires (max_auction_trace(st, xs) <=> true))
_(requires st.acode == Running && st.identity == sid && st.quote == sqt)
_(ensures exists_a_bid_gt_than_reserve(resvalue, xs) == 0)
_(lemma) _(pure)
{
  if(xs == nil)
  {
    _(assert exists_a_bid_gt_than_reserve(resvalue, nil) == 0)
  }
  else
  {
    _(assert exists struct auction_event y, list<struct auction_event> ys. cons(y, ys) == xs)
    if(y == st)
    {
      // This is a winning, but still lower than the minimum supporting value, resvalue
      _(assert exists int yid. yid == y.identity)
      _(assert exists int yqt. yqt == y.quote)
      _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 
           ((y.quote >= resvalue) ? 1 : (exists_a_bid_gt_than_reserve(resvalue, ys))))
      _(assert yqt == sqt)
      _(assert yqt < resvalue)
      _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == exists_a_bid_gt_than_reserve(resvalue, ys))
      _(apply max_auction_true_case(st, y, ys, xs);)
      _(assert max_auction_trace(st, ys) <=> true)
      exists_bid_equal_met_false_case(sid, sqt, resvalue, st, ys);
    }
    else
    {
      _(assert y != st)
      _(assert exists int yid. yid == y.identity)
      _(assert exists int yqt. yqt == y.quote)
      _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == 
           ((y.quote >= resvalue) ? 1 : (exists_a_bid_gt_than_reserve(resvalue, ys))))


      /* There are two situations: 
        1. yqt > sqt -> But this cannot happen because sqt is the bigger one 
        2. yqt <= sqt -> yqt < resvalue and keep searching */

      if (yqt > sqt)
      {
        _(assert yqt > sqt)
        _(assert max_auction_trace(st, cons(y, ys)) <=> false) 
        _(assert false) 
      }
      else
      {
        _(assert yqt <= sqt)
        _(assert yqt < resvalue)
        _(assert exists_a_bid_gt_than_reserve(resvalue, cons(y, ys)) == exists_a_bid_gt_than_reserve(resvalue, ys))
        _(apply max_auction_true_case(st, y, ys, xs);)
        _(assert max_auction_trace(st, ys) <=> true)
        exists_bid_equal_met_false_case(sid, sqt, resvalue, st, ys);
        
      }
    }
  }
}

void  exists_bid_equal_met(int met, int sid, int sqt, int resvalue, struct auction_event st, struct auction_event x, list<struct auction_event> xs, list<struct auction_event> ios)
_(requires met == 0 || met == 1)
_(requires met == abs_to_int(sqt >= resvalue))
_(requires ios == cons(x, xs))
_(requires x.acode == Finished)
_(requires (member(st, xs) <=> true))
_(requires st.acode == Running && st.identity == sid && st.quote == sqt)
_(requires (max_auction_trace(st, xs) <=> true))
_(ensures met == exists_a_bid_gt_than_reserve(resvalue, xs))
_(lemma) _(pure)
{
    _(apply 
        if (met == 1)
        {

          _(assert abs_to_int(sqt >= resvalue) == 1)
          _(apply proof_of_first_gt(sqt, resvalue);)
          _(assert sqt >= resvalue)
          
          /* Now I know that the bid st quote, sqt, is greater resvalue, 
           so we can conclude that exists_a_bid_gt_than_reserve(resvalue, ios) == 1 
           and we are home */
          _(apply exists_bid_equal_met_true_case(sid, sqt, resvalue, st, xs);)
          _(assert exists_a_bid_gt_than_reserve(resvalue, xs) == 1)
        }
        else
        {
          _(assert abs_to_int(sqt >= resvalue) == 0)
          _(apply proof_of_second_gt(sqt, resvalue);)
          _(assert sqt < resvalue)

          /* Unfortunately, the maximum bid's quote, sqt, is less than the 
          minimum supporting value, resvalue, hence we conclude that 
          exists_a_bid_gt_than_reserve(resvalue, ios) ==  0 and we 
          are home */
          _(apply exists_bid_equal_met_false_case(sid, sqt, resvalue, st, xs);)
          _(assert exists_a_bid_gt_than_reserve(resvalue, xs) == 0)
        })
  }




void abs_to_int_lemma(int a, int b, int t)
_(requires t == abs_to_int(a >= b))
_(ensures t == 0 || t == 1)
_(lemma) _(pure)
{
  if (a < b)
  {
    _(apply abs_to_int_lt_proof(a, b, t);)
  }
  else
  {
    _(apply abs_to_int_gt_proof(a, b, t);)
  }

}


void proof_of_first_gt(int a, int b)
_(requires abs_to_int(a >= b) == 1)
_(ensures a >= b)
_(lemma) _(pure)
{

    if(a >= b)
    {
      _(assert abs_to_int(a >= b) == 1)

    }
    else
    {
      _(assert a < b)
      _(assert (a >= b) == false)
      _(assert abs_to_int(false) == 0)
      _(assert false)
    }

}


void proof_of_second_gt(int a, int b)
_(requires abs_to_int(a >= b) == 0)
_(ensures a < b)
_(lemma) _(pure)
{

    if(a >= b)
    {
      _(assert abs_to_int(true) == 1)
      _(assert false)

    }
    else
    {
      _(assert a < b)
      _(assert (a >= b) == false)
      _(assert abs_to_int(false) == 0)
    }

}

#endif


int is_first_gt_second(int a, int b)
_(ensures result == abs_to_int (a >= b))
_(ensures result == 0 || result == 1)
{
  int t = to_int(a >= b);
  _(assert t == abs_to_int(a >= b))
  _(apply abs_to_int_lemma(a, b, t);)
  _(assert t == 0 || t == 1)
  return t;
}



/* This function simply closes the auction */
status_code close_auction(struct id_and_quote *s, database_status *d) 
_(requires exists list<struct auction_event> ios. io_trace(;ios))
_(requires auction_database_inv(s, d; ios))
_(ensures result :: low)
_(ensures result == Success || result == Failure)
_(ensures exists list<struct auction_event> iost. io_trace(; iost))
_(ensures result == Success ==> exists struct auction_event e. 
      e.acode == Finished && iost == cons(e, ios))     
_(ensures result == Failure ==> iost == ios)
_(ensures auction_database_inv(s, d; iost))
{

  _(unfold auction_database_inv(s, d; ios))
  _(assert exists int id, int qt, database_status alpha.
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed))

    database_status stp = *d;
    if(stp == Ready)
    {
      // The auction has not started yet 
      // so there is no point of closing it
      _(fold auction_database_inv(s, d; ios))
      return Failure;

    }
    else if (stp == Closed)
    {
      // The auction is closed so there is 
      // no point of closing it again
      _(fold auction_database_inv(s, d; ios))
      return Failure;
    }
    else
    {
      _(assert exists struct auction_event st. 
        (member(st, ios) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, ios) <=> true))
      _(apply no_finished_trace_in_start_or_ongoing_state(s, d, ios, id, qt, alpha);)
      *d = Closed;
      

      
      struct auction_event e = bid_closed_log();
      _(assert exists struct auction_event e. io_trace(;cons(e, ios)) &&
          e.acode == Finished)
      _(assert exists list<struct auction_event> iost. iost == cons(e, ios) && 
          io_trace(;iost))
      
      
      _(assert iost == cons(e, ios) &&
          e.acode == Finished &&
          (member(st, ios) <=> true) &&
          st.acode == Running && st.identity == id && st.quote == qt &&
          (max_auction_trace(st, ios) <=> true))

       _(fold auction_database_inv(s, d; iost))
       return Success;
      
    }
}


/* This function assumes that auction is close (You can use close_auction function to close the auction )*/
status_code successful_only_if_exists_a_bid_greater_than_the_reserve_bid(struct id_and_quote *s, database_status *d, int *res, int *p, int *q)
_(requires exists list<struct auction_event> ios. io_trace(;ios))
_(requires auction_database_inv(s, d; ios))
_(requires exists int reserve. res |-> reserve)
_(requires reserve_predicate(;reserve))
_(requires exists int opval. p |-> opval)
_(requires exists int oqval. q |-> oqval)
_(ensures result :: low)
_(ensures result == Success || result == Failure)
_(ensures result == Failure ==> p |-> opval)
_(ensures result == Failure ==> q |-> oqval)
_(ensures result == Success ==> exists int npval. p |-> npval && npval :: low) 
_(ensures result == Success ==> exists int nqval. q |-> nqval && nqval :: low)
_(ensures res |-> reserve)
_(ensures auction_database_inv(s, d; ios))
_(ensures io_trace(;ios))
_(ensures reserve_predicate(;reserve))
{

  _(unfold auction_database_inv(s, d; ios))
  _(assert exists int id, int qt, database_status alpha.
    &s->id |-> id &&
    &s->qt |-> qt &&
    d |-> alpha &&  (alpha :: low) &&
    (alpha == Ready || alpha == Ongoing || alpha == Closed))

  database_status stp = *d;
  if(stp == Ready)
  {
    // The auction has not started yet 
    // so there is no point of checking
    // that winning bid is greater than
    // the reserve bid.
    _(fold auction_database_inv(s, d; ios))
    return Failure;

  }
  else if (stp == Ongoing)
  {
    // The auction is ongoing so there is 
    // no point of checking that winning 
    // bid is greater than the reserve bid.
    _(fold auction_database_inv(s, d; ios))
    return Failure;
  }
  else
  {

    
    // The auction is closed, and we would like
    // to make sure that when declassifying the 
    // winning bid, it is more than the  
    // reserve value. Otherwise, we don't 
    // declassify anything
    _(assert stp == Closed)
    _(assert exists struct auction_event st, struct auction_event x,
        list<struct auction_event> xs.  
        ios == cons(x, xs) &&
        x.acode == Finished &&
        (member(st, xs) <=> true) &&
        st.acode == Running && st.identity == id && st.quote == qt &&
        (max_auction_trace(st, xs) <=> true))
    
    int resvalue = *res;
    int sid = s->id;
    int sqt = s->qt;
    int met = is_first_gt_second(sqt, resvalue);
    _(assert met == abs_to_int(sqt >= resvalue))
    _(assert met == 0 || met == 1) 
    
    /* 
      Here we are doing two declassification:
      1. declassifying the result of if the largest bid is greater-or-equal to the reserve (sqt >= resvalue)
      2. If so, we declassify the largest bid

      One of the nicest thing about this is that is compositional, and a programmer can compose many 
      such policies.  
    */
    _(assert sid == id)
    _(assert sqt == qt)
    _(assert reserve == resvalue)
    _(apply exists_reserve_0_1(resvalue, xs);)
    _(assert (exists_a_bid_gt_than_reserve(resvalue, xs) == 0 || 
        exists_a_bid_gt_than_reserve(resvalue, xs) == 1)) 
    _(apply exists_bid_equal_met(met, sid, sqt, resvalue, st, x, xs, ios);)
    _(assert met == exists_a_bid_gt_than_reserve(resvalue, xs))
      
    /* start of manual inspection
       we declassify this bit and based on this bit, 
       we decide if the declassification of winning 
       bid would happen or not. */
    _(fold safe_to_release_bit(;met, resvalue, x, xs, ios))    
    _(assume met :: low)  
    // end of manual inspection
    _(unfold safe_to_release_bit(;met, resvalue, x, xs, ios))        
    if (met == 1)
    {

      *p = s->id;
      *q = s->qt;

      _(apply proof_of_first_gt(sqt, resvalue);)
      _(assert sqt >= resvalue)
      _(assert met == 1)
      _(fold safe_to_declassify_bid(sid, sqt, ios))
      _(assert reserve_predicate(;resvalue))
      _(fold safe_to_declassify_when_reserve_met(;met, resvalue, sid, sqt, ios))
      // start of manual inspection
      _(assume sid :: low)
      _(assume sqt :: low)
      //end of manual inspection
      _(unfold safe_to_declassify_when_reserve_met(;met, resvalue, sid, sqt, ios))
      _(unfold safe_to_declassify_bid(sid, sqt, ios))
      _(fold auction_database_inv(s, d; ios))
      return Success;           
    }
    else
    {

      _(assert met == 0)
      _(fold auction_database_inv(s, d; ios))
      return Failure;
    } 
    
  }

}




struct id_and_quote *s;
database_status *d;

void acquire_lock();
_(ensures exists list<struct auction_event> ios. 
    io_trace(;ios))
_(ensures auction_database_inv(s, d; ios))    

void release_lock();
_(requires exists list<struct auction_event> ios. 
    io_trace(;ios))
_(requires auction_database_inv(s, d; ios))  


void write_bid_in_the_database_thread(struct id_and_quote *bid)
_(requires exists int _bidid, int _bidqt. &bid->id |-> _bidid && &bid->qt |-> _bidqt)
_(ensures &bid->id |-> _bidid && &bid->qt |-> _bidqt)

{
    
      acquire_lock();
      _(assert exists list<struct auction_event> ios. io_trace(;ios))
      _(assert auction_database_inv(s, d; ios))
      register_bid(s, d, bid);
      release_lock();
  
}

void sleep(int delay);
_(requires delay :: low)

// XXX: exit doesn't return so maybe its postcondition should say false? 
void exit(int status);
_(requires status :: low)

void print_winner(int id, int quote);
_(requires id :: low && quote :: low)

void close_and_declassify_bid_thread(int delay, int *p , int *q)
_(requires delay :: low)
_(requires exists int v. p |-> v)
_(requires exists int w. q |-> w)
_(ensures exists int vn. p |-> vn && vn :: low)
_(ensures exists int wn. q |-> wn && wn :: low)
{
      *p = 0;
      *q = 0;
      sleep(delay);
      acquire_lock();
      _(assert exists list<struct auction_event> ios. io_trace(;ios))
      _(assert auction_database_inv(s, d; ios))
      status_code c = close_auction_and_declassify(s, d, p, q);
      release_lock();
      if (c == Success)
        print_winner(*p, *q);
      exit(0);
}


void close_and_declassify_if_gt_resvalue(int delay, int *p, int *q, int *res)
_(requires delay :: low)
_(requires exists int resvalue. res |-> resvalue)
_(requires reserve_predicate(;resvalue))
_(requires exists int v. p |-> v)
_(requires exists int w. q |-> w)
_(ensures exists int vn. p |-> vn && vn :: low)
_(ensures exists int wn. q |-> wn && wn :: low)
_(ensures res |-> resvalue)
_(ensures reserve_predicate(;resvalue))
{
      *p = 0;
      *q = 0;
      sleep(delay);
      acquire_lock();
      _(assert exists list<struct auction_event> ios. io_trace(;ios))
      _(assert auction_database_inv(s, d; ios))
      status_code c;
      status_code ret;
      c = close_auction(s, d);
      if (c == Success)
      {
        ret = successful_only_if_exists_a_bid_greater_than_the_reserve_bid(s, d, res, p, q);
        _(assert ret == Success || ret == Failure)
        if (ret == Success)
        print_winner(*p, *q);
      }
      release_lock();
      exit(0);
}
