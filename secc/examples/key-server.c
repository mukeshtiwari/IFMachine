#include "secc.h"

typedef int email_address;
typedef int token;
typedef int public_key;

enum email_code
{
  /* registration no defined */ 
  registration_undefined,
  /* register initialisation */
  registration_initiated,
  /* register confirmation */
  registration_confirmed
};
typedef enum email_code registration_state;


struct state {
  email_address stored_address;
  token stored_token;
  registration_state state;
  public_key pub_key;
};



struct event
{
  email_address email;
  token t;
};

enum ret_code 
{
  Failure,
  Success
};
typedef enum ret_code status_code;


_(predicate io_trace(;list<struct event> xs))

_(function
	list<struct event> append(list<struct event> xs, list<struct event> ys))

_(rewrites
	forall list<struct event> ys. append(nil, ys) == ys;
	forall struct event x, list<struct event> xs, list<struct event> ys.
		append(cons(x, xs), ys) == cons(x, append(xs, ys)))



void append_associative(list<struct event> xs, list<struct event> ys, list<struct event> zs)
_(ensures  append (xs, append(ys, zs)) ==  append(append (xs, ys), zs))
_(lemma) _(pure)
{
  
  if (xs == nil)
  {
    _(assert append(nil, append(ys, zs)) == append(append(nil, ys), zs))
    return;
  }
  else 
  {
    _(assert exists struct event t, list<struct event> ts. xs == cons(t, ts))
    append_associative(ts, ys, zs);
    return;
  }

} 



_(function bool search_trace(email_address addr, token t, list<struct event> ios))

_(rewrites 
      forall email_address addr, token t. search_trace(addr, t, nil) <=> false;
      forall email_address addr, token t, struct event x, list<struct event> xs. 
        search_trace(addr, t, cons (x, xs)) <=> 
           ((x.email == addr) ? (x.t == t) : (search_trace(addr, t, xs))))





_(function int length(list<struct event> ios))

_(rewrites 
      length(nil) == 0;
      forall struct event x, list<struct event> xs. length(cons(x, xs)) == 1 + length(xs)) 


_(predicate length_is_low(; list<struct event> ios) 
    (ios == nil :: low) && 
    (ios == nil ? true : (exists struct event e, list<struct event> es. ios == cons(e, es) && length_is_low(; es))))


void length_is_low_lemma(struct event e, list<struct event> ios)
_(requires length_is_low(;ios))
_(ensures length_is_low(;cons(e, ios)))
_(lemma)
{
  _(fold length_is_low(;cons(e,ios)))
}


_(function int search_trace_int(email_address addr, token t, list<struct event> ios))


_(rewrites
      forall email_address addr, token t. search_trace_int(addr, t, nil) == -1;

      forall email_address addr, token t, struct event x, list<struct event> xs.
         search_trace_int(addr, t, cons(x, xs)) ==
         ((x.email == addr) ? (x.t == t ? 0 : -1) : 
            ((search_trace_int(addr, t, xs) == -1) ? -1 : (1 + search_trace_int(addr, t, xs)))))




void ios_is_not_nil(email_address addr, token t, list<struct event> ios)
_(requires search_trace_int(addr, t, ios) >= 0)
_(ensures exists struct event e, list<struct event> es. ios == cons(e, es))
_(pure) _(lemma)
{
   if(ios == nil)
   {
     _(assert search_trace_int(addr, t, nil) == -1)
     return;
   }
   else 
   {
     _(assert exists struct event e, list<struct event> es. ios == cons(e, es))
     return;
   }
}



void search_trace_int_0(email_address addr, token t, list<struct event> ios)
_(requires search_trace_int(addr, t, ios) == 0)
_(ensures exists struct event e, list<struct event> es. ios == cons(e, es) &&
  e.email == addr && e.t == t)
_(pure) _(lemma)
{
  if (ios == nil)
  {
    
      _(assert search_trace_int(addr,t,ios) == -1)
  }
  else
  {
      _(assert exists struct event e, list<struct event> es. cons(e,es) == ios)
      _(assert exists email_address ev. e.email == ev)
      _(assert exists token tv. e.t == tv) 
      /* For Gidon: 
          If we replace ev with e.email, then we get exception: 
           Exception in thread "main" scala.MatchError: e.email (of class secc.c.Dot) */     
      if (ev == addr)
      {
        if (tv == t)
        {
            _(assert search_trace_int(addr,t,cons(e,es)) == 0)
        }
        else
        {
            _(assert search_trace_int(addr,t,cons(e,es)) == -1)
            _(assert false)
        }
      }
    else
    {
        _(assert exists int v. search_trace_int(addr,t,es) == v)
        /* If we write v == -1, then we get error:
            Exception in thread "main" scala.MatchError: (- 1) (of class secc.c.PreOp) */
        if (v == (0-1))
        {
          _(assert search_trace_int(addr,t,cons(e,es)) == -1)
          _(assert false)
        }
       else
       {
          _(assert search_trace_int(addr,t,es) != -1)
          _(assert search_trace_int(addr,t,cons(e,es)) == 1 + search_trace_int(addr,t,es))
          _(assert search_trace_int(addr,t,cons(e,es)) != 0)
          _(assert false)
       }
    }
  }
}



void search_trace_int_gr_0(email_address addr, token t, list<struct event> ios)
_(requires search_trace_int(addr, t, ios) > 0)
_(ensures exists struct event e, list<struct event> es. ios == cons(e, es) && e.email != addr)
_(pure) _(lemma)
{
  if(ios == nil)
  {
    _(assert search_trace_int(addr, t, nil) == -1)
    _(assert false)
    
  }
  else 
  {
      _(assert exists struct event e, list<struct event> es. cons(e,es) == ios)
      _(assert exists email_address ev. e.email == ev)
      _(assert exists token tv. e.t == tv) 
      
      if(ev == addr)
      {
          if(tv == t)
          {
            _(assert search_trace_int(addr, t, cons(e, es)) == 0)
            _(assert false)

          }
          else
          {
            _(assert tv != t)
            _(assert search_trace_int(addr, t, cons(e, es)) == -1)
            _(assert false)

          }

      }
      else
      {
          _(assert ev != addr)
          
          _(assert exists int v. search_trace_int(addr, t, es) == v)
          if(v == (0-1))
          {
              _(assert search_trace_int(addr, t, cons(e,es)) == -1)
              _(assert false)
          }
          else
          {
              _(assert search_trace_int(addr, t, es) != -1)
              _(assert search_trace_int(addr,t,cons(e,es)) == 1 + search_trace_int(addr,t,es))
              _(assert search_trace_int(addr,t,cons(e,es)) > 0) 
        }       
      }
  }

} 


void search_trace_int_low(email_address addr, token t, list<struct event> ios)
_(requires exists int n. n >= 0 && n :: low)
_(requires search_trace_int(addr, t, ios) == n)
_(ensures exists struct event io, list<struct event> tl. ios == cons(io, tl))
_(ensures io.email == addr :: low)
_(lemma)
{
  _(apply 
      if(n == 0)
      {
          search_trace_int_0(addr, t, ios);
          return;

      }
      else
      {
          search_trace_int_gr_0(addr, t, ios);
          return;
      })
}



/* If I make n as a existentailly quantified, then SecC won't be able to prove this lemma. */
void search_true_int(email_address addr, token t, list<struct event> ios, int n)
_(requires length_is_low(;ios))
_(requires n >= 0 && n :: low)
_(requires search_trace_int(addr, t, ios) == n)
_(ensures length_is_low(;ios))
_(ensures exists struct event p, list<struct event> lr, list<struct event> rr. 
   (ios == append (lr, cons(p, rr))) &&  p.email == addr && p.t == t && 
   (length(lr) == n) &&
   (forall token tp. search_trace_int(addr, tp, lr) == -1))
_(lemma)
{
  _(unfold length_is_low(;ios))
  _(assert ios == nil :: low)
  _(assert (ios == nil ? true : (exists struct event e, list<struct event> es. ios == cons(e, es) && length_is_low(; es))))
  if(ios == nil)
  {
      _(assert ios == nil)
      _(assert search_trace_int(addr, t, nil) == -1)
      _(fold length_is_low(;nil))
      return;
  }
  else 
  {
    _(assert exists struct event y, list<struct event> ys. ios == cons(y, ys))
    _(assert exists email_address u, token v. y.email == u && y.t == v)
    _(assert length_is_low(; ys))
    _(assert search_trace_int(addr, t, cons(y, ys)) ==
            ((y.email == addr) ? (y.t == t ? 0 : -1) : 
            ((search_trace_int(addr, t, ys) == -1) ? -1 : (1 + search_trace_int(addr, t, ys)))))

    
    search_trace_int_low(addr, t, ios);
    
    if (addr == u)
    {
      
        if (t == v)
        {
              //We have found an element at the head of the list
              //Success;
              _(assert y.email == addr)
              _(assert y.t == t)
              _(assert search_trace_int(addr, t, cons(y, ys)) == 0)
              _(assert ios == append(nil, cons(y, ys)))
              _(assert addr == u && t == v)
              _(assert length(nil) == 0)
              _(assert forall int xw. search_trace_int(addr, xw, nil) == -1)
        }
        else 
        {
              // Failure
              // We have matched the email address, but token given was not correct
              _(assert t != v)
              _(assert addr == u && t != v)
              _(assert y.email == addr && y.t != t)
              _(assert search_trace_int(addr, t, cons(y, ys)) == -1)
              _(assert length(nil) == 0)
              _(assert forall int xw. search_trace_int(addr, xw, nil) == -1)

        }
        _(fold length_is_low(;cons(y, ys)))
        return;
    }
    else 
    {
        
            _(assert addr != u)
            _(assert y.email != addr)
            _(assert search_trace_int(addr, t, cons(y, ys)) == n && n >= 0)

            _(assert exists int v. search_trace_int(addr, t, ys) == v &&  v >= 0)
            _(assert search_trace_int(addr, t, ys) != -1)
            _(assert search_trace_int(addr, t, cons(y, ys)) == 1 + search_trace_int(addr, t, ys))
           
            search_true_int(addr, t, ys, n-1);
           
            _(assert v >= 0)
            _(assert 1 + v == n)
            _(assert length(cons(y, ys)) == 1 + length(ys))
            _(assert search_trace_int(addr, t, ys) == v ==>
                (exists struct event p, list<struct event> lr, list<struct event> rr.
                    (ys == append(lr, cons(p, rr))) &&
                    (ios == append(cons(y, lr), cons(p, rr))) &&           
                    (p.email == addr && p.t == t) && 
                    (length(cons(y, lr)) == 1 + v)  &&
                    (forall int tw. search_trace_int(addr, tw, lr) == -1)) &&
                    (forall int tw. search_trace_int(addr, tw, cons(y, lr)) == -1))
                         
        _(fold length_is_low(;cons(y, ys)))
        return;

    }
  }
}




_(function bool search_email(email_address addr, list<email_address> prevs))

_(rewrites  
    forall email_address addr. search_email(addr, nil) <=> false; 
    forall email_address addr, email_address hprev, list<email_address> prevs. 
       (search_email(addr, cons(hprev, prevs)) <=> ((addr == hprev) ? true : search_email(addr, prevs))))

 

_(predicate ar_sec_undefined(struct state *a, int n)
  (n > 0 ==> exists email_address addr, token tok, registration_state c, public_key pubkey. 
      &a->stored_address |-> addr && &a->stored_token |-> tok && &a->state |-> c &&  
      &a->pub_key |-> pubkey  && 
      (c :: low) && (c == registration_undefined) && ar_sec_undefined(a+1, n-1)))



_(predicate ar_sec(struct state *a, int n; list<struct event> iost, list<email_address> prevs)
  (n > 0 ==> exists email_address addr, token tok, registration_state c, public_key pubkey. 
      &a->stored_address |-> addr && &a->stored_token |-> tok && &a->state |-> c &&  
      &a->pub_key |-> pubkey  && 
      (c :: low) && 
      (c == registration_undefined || c == registration_initiated || c == registration_confirmed) &&
      (c == registration_undefined ==> ar_sec_undefined(a+1, n-1))  &&     
      (c == registration_initiated ==> (exists int w. search_trace_int(addr, tok, iost) == w && w >= 0 && w :: low)  && 
          (search_email(addr, prevs) <=> false) && ar_sec(a+1, n-1; iost, cons(addr, prevs)))  &&
      (c == registration_confirmed ==>  (addr :: low) && (search_email(addr, prevs) <=> false) && 
          ar_sec(a+1, n-1; iost, cons(addr, prevs))))) 



void ar_sec_undefined_implies_ar_sec(struct state *a, int n, list<struct event> ios, list<email_address> prevs)
   _(requires n >= 0 && n :: low)
   _(requires ar_sec_undefined(a, n))
   _(ensures ar_sec(a, n; ios, prevs))
   _(lemma)
  {
      if(n == 0)
      {
        _(unfold ar_sec_undefined(a, 0))
        _(fold ar_sec(a, 0; ios, prevs))
        return;
      }
      else
      {
          _(unfold ar_sec_undefined(a, n))
          _(assert exists email_address addr, token tok, registration_state c, public_key pubkey. 
                &a->stored_address |-> addr && &a->stored_token |-> tok && &a->state |-> c &&  
                &a->pub_key |-> pubkey  && 
                (c :: low) && (c == registration_undefined) && ar_sec_undefined(a+1, n-1))
          _(fold ar_sec(a, n; ios, prevs))
          return;
      }
  }  




void ar_sec_correct(struct state *s, int n, struct event e, list<struct event> ios)
   _(requires n >= 0 && n :: low)
   _(requires exists list<email_address> prevs. ar_sec(s, n; ios, prevs))
   _(requires (search_email(e.email, prevs) <=> true))
   _(ensures ar_sec(s, n; cons(e, ios), prevs))
   _(lemma)
   {
     _(unfold ar_sec(s, n; ios, prevs))
     if(n == 0)
     {
       _(fold ar_sec(s, 0; cons(e, ios), prevs))
       return;

     }
     else 
     {
       
       _(assert exists email_address addr, token tok, registration_state c, public_key pubkey. 
          &s->stored_address |-> addr && &s->stored_token |-> tok && &s->state |-> c &&  
          &s->pub_key |-> pubkey)
       _(assert c == registration_undefined || c == registration_initiated || c == registration_confirmed)
       _(apply 
        if (c == registration_undefined)
          {
               
              _(fold ar_sec(s, n; cons(e, ios), prevs))
              
          }
          else if (c == registration_initiated)
          {
            
            
                _(assert exists int w. search_trace_int(addr, tok, ios) == w && w >= 0)
                _(assert search_email(addr, prevs) <=> false)
                _(assert e.email != addr)
                ar_sec_correct(s+1, n-1, e, ios);
                _(fold ar_sec(s, n; cons(e, ios), prevs)) 
              
          

          }
          else 
          {
                _(assert c == registration_confirmed)     
                _(assert search_email(addr, prevs) <=> false)
                _(assert e.email != addr)
                 ar_sec_correct(s+1, n-1, e, ios);
                _(fold ar_sec(s, n; cons(e, ios), prevs))

          })

        return;
     }

   } 
   




// When I am going to declassify, I need to make sure that search_trace return true for 
// email and t. What does this mean is there is a trace ios == ls ++ [p] ++ rs
// such p hold the <email, t> 

_(predicate safe_to_declassify_email_ios(email_address email, token t, list<struct event> ios)
   (exists list<struct event> ls, list<struct event> rs, struct event p. 
      io_trace(;ios) &&
      ios == append (ls, cons(p, rs)) && p.email == email && p.t == t))

   


token new_token(email_address addr);
_(requires exists list<struct event> ios. io_trace(; ios))
_(ensures exists struct event e. io_trace(; cons(e, ios)) &&
    e.email == addr && e.t == result)



status_code register_email(struct state *s, int n, email_address addr, public_key pubkey, token *p)
_(requires n >= 0 && n :: low)
_(requires exists list<struct event> ios. io_trace(; ios))
_(requires exists list<email_address> prevs. ar_sec(s, n; ios, prevs))
_(requires exists token vorig. p |-> vorig)
_(requires (search_email(addr, prevs) <=> false))
_(requires length_is_low(;ios))
_(ensures result :: low)
_(ensures result == Success || result == Failure)
_(ensures exists token vnew. p |-> vnew)
_(ensures result == Failure ==> vorig == vnew)
_(ensures exists list<struct event> iost. io_trace(; iost))
_(ensures ar_sec(s, n; iost, prevs))
_(ensures result == Success ==> exists struct event e. iost == cons(e, ios) && e.email == addr && e.t == vnew)
_(ensures result == Failure ==> iost == ios)
_(ensures length_is_low(;iost))
{

  if(n == 0)
  {
    // We have reached to the end of database and there 
    // is no empty spot
    _(unfold ar_sec(s, 0; ios, prevs))
    _(fold ar_sec(s, 0; ios, prevs))
    return Failure;
  }
  else 
  {
      // Let's inspect the database
      _(unfold ar_sec(s, n; ios, prevs))
      _(assert exists email_address adt, token tk, registration_state cc, public_key pkey. 
        &s->stored_address |-> adt && &s->stored_token |-> tk && &s->state |-> cc &&  
        &s->pub_key |-> pkey)
     _(assert cc == registration_undefined || cc == registration_initiated || cc == registration_confirmed)   
    
    registration_state st = s->state;

    if (st == registration_undefined)
    {
          _(assert cc == registration_undefined)

          s->stored_address = addr;
          token t = new_token(addr);
          s->stored_token = t;
          s->state = registration_initiated;
          s->pub_key = pubkey;
          *p = t;

          _(assert exists struct event e. io_trace(; cons(e, ios)) && e.t == t && e.email == addr)
          _(assert &s->stored_address |-> e.email)
          _(assert ar_sec_undefined(s+1, n-1))
          _(apply ar_sec_undefined_implies_ar_sec(s+1, n-1, ios, cons(addr, prevs));)
          _(apply ar_sec_correct(s+1, n-1, e, ios);)
          _(apply length_is_low_lemma(e, ios);)
          _(fold ar_sec(s, n; cons(e, ios), prevs))
          return Success;

    }
    else if (st == registration_initiated)
    {
        email_address ed = s->stored_address;

       _(assume ed == addr :: low)

        if(ed == addr)
        {
          _(assert ed == addr)
          token t = new_token(addr);
          s->stored_token = t;
          s->pub_key = pubkey;
          *p = t;

          _(assert exists struct event e. io_trace(; cons(e, ios)) && e.t == t && e.email == addr)
          _(assert search_email(e.email, prevs) <=> false)   
          _(apply ar_sec_correct(s+1, n-1, e, ios);)
          _(apply length_is_low_lemma(e, ios);)
          _(fold ar_sec(s, n; cons(e, ios), prevs))
          return Success;   

        }
        else 
        {
          _(assert ed != addr)
          status_code sta = register_email(s+1, n-1, addr, pubkey, p);
          if(sta == Success)
           {
                _(assert sta == Success ==> exists struct event e, list<struct event> iost. io_trace(;iost) && iost == cons(e, ios))
                _(fold ar_sec(s, n; iost, prevs))
                return sta;

          }
          else 
          {
                _(assert sta == Failure ==> exists list<struct event> iost. io_trace(;iost) && iost == ios)
                _(fold ar_sec(s, n; iost, prevs))
                return sta;
          }
        }
    }
    else 
    {
        _(assert st == registration_confirmed)
  
        email_address ed = s->stored_address;
        _(assume ed == addr :: low)
        if(ed == addr)
        {
           // You are not allowed to do a re-registration for already registered 
           // email
            _(fold ar_sec(s, n; ios, prevs))
            return Failure;

        }
        else 
        {
            _(assert ed != addr)
            status_code sta = register_email(s+1, n-1, addr, pubkey, p);
             if(sta == Success)
              {
                    _(assert sta == Success ==> exists struct event e, list<struct event> iost. io_trace(;iost) && iost == cons(e, ios))
                    _(fold ar_sec(s, n; iost, prevs))
                    return sta;
              }
              else 
              {
                    _(assert sta == Failure ==> exists list<struct event> iost. io_trace(;iost) && iost == ios)
                    _(fold ar_sec(s, n; iost, prevs))
                    return sta;
              }           
        }
    }
  }
} 

 



/* confirm would took through a list of io traces (non empty), 
   and search through the traces to find where the token "t" is.  */

status_code confirm_email(struct state *s, int n, email_address addr, token t)
_(requires n >= 0 && n :: low)
_(requires exists list<struct event> ios. io_trace(;ios))
_(requires length_is_low(;ios))
_(requires exists list<email_address> prevs. ar_sec(s, n; ios, prevs))
_(ensures result :: low)
_(ensures result == Success || result == Failure)
_(ensures ar_sec(s, n; ios, prevs))
_(ensures io_trace(; ios))
_(ensures length_is_low(;ios))
{

   if(n == 0)
    {
        _(unfold ar_sec(s, 0; ios, prevs))
        _(fold ar_sec(s, 0; ios, prevs)) 
        return Failure;
  }
  else 
  {

      _(unfold ar_sec(s, n; ios, prevs))
      _(assert exists email_address adt, token tk, registration_state cc, public_key pkey. 
        &s->stored_address |-> adt && &s->stored_token |-> tk && &s->state |-> cc &&  
        &s->pub_key |-> pkey)
     _(assert cc == registration_undefined || cc == registration_initiated || cc == registration_confirmed)   
    
    registration_state st = s->state;

    
    if(st == registration_undefined)
    {
        // do nothing and return failure because everything after this is undefined
        _(fold ar_sec(s, n; ios, prevs))
        return Failure;
    }
    else if (st == registration_initiated)
    {
        email_address ed = s->stored_address;
        _(assume ed == addr :: low)

        if(ed == addr)
        {
            token et = s->stored_token;
            _(assume et == t :: low)
            if(et == t)
            {
                // happy case and make the emaill address low
                _(assert &s->stored_address |-> addr)
                _(assert &s->state |-> registration_initiated)
                _(assert &s->stored_token |-> t)
                _(assert n > 0)

                _(assert exists int w. search_trace_int(addr, t, ios) == w)
                _(apply search_true_int(addr, t, ios, w);)
                _(assert exists list<struct event> ls, list<struct event> rs, struct event p. 
                    io_trace(;ios) &&
                    ios == append (ls, cons(p, rs)) && p.email == addr && p.t == t)

                s->state = registration_confirmed;
                // Now that registration is confirmed, we can safely declassify 
                // the email address of registrant
                _(fold safe_to_declassify_email_ios(addr, t, ios))
                _(assume addr :: low)
                _(unfold safe_to_declassify_email_ios(addr,t,ios))
                _(fold ar_sec(s, n; ios, prevs))
                return Success;
            }
            else 
            {
               _(assert et != t)
              _(fold ar_sec(s, n; ios, prevs))
              return Failure;

            }
        }
        else
        {
            // look for next spot
             status_code sc = confirm_email(s+1, n-1, addr, t);
            _(fold ar_sec(s, n; ios, prevs)) 
            return sc;
        }       

    }
    else
    {
      _(assert st == registration_confirmed)
      // this is already taken by some one, so continue looking for next
       status_code sc = confirm_email(s+1, n-1, addr, t);
      _(fold ar_sec(s, n; ios, prevs)) 
      return sc;

    } 
  } 
}




/* returns the public key related to confirmed email address */

status_code get_key_by_email(struct state *s, int n, email_address addr, public_key *p)
 _(requires exists list<struct event> ios. io_trace(;ios))
 _(requires n >= 0 && n :: low)
 _(requires exists list<email_address> prevs. ar_sec(s, n; ios, prevs))
 _(requires exists public_key vorig. p |-> vorig)
 _(requires length_is_low(;ios))
 _(ensures ar_sec(s, n; ios, prevs))
 _(ensures io_trace(;ios))
 _(ensures result :: low)
 _(ensures result == Success || result == Failure)
 _(ensures exists public_key vnew. p |-> vnew)
 _(ensures result == Failure ==> vorig == vnew)
 _(ensures length_is_low(;ios))
 {

    if(n == 0)
    {
        _(unfold ar_sec(s, 0; ios, prevs))
        _(fold ar_sec(s, 0; ios, prevs))
        return Failure;
   }
   else 
   {
        _(unfold ar_sec(s, n; ios, prevs))
        _(assert exists email_address adt, token tk, registration_state cc, public_key pkey. 
            &s->stored_address |-> adt && &s->stored_token |-> tk && &s->state |-> cc &&  
            &s->pub_key |-> pkey)
        _(assert cc == registration_undefined || cc == registration_initiated || cc == registration_confirmed)   
    
        registration_state st = s->state;

        
        if(st == registration_undefined)
        {
              // hopeless situation because everything is undefined after this
              _(fold ar_sec(s, n; ios, prevs))
              return Failure; 
        }
        else if (st == registration_initiated)
        {
              status_code ret = get_key_by_email(s+1, n-1, addr, p);
              _(fold ar_sec(s, n; ios, prevs))
              return ret; 

        }
        else 
        {
            _(assert st == registration_confirmed)
            // this is the place where we should be looking
            email_address ed = s->stored_address;
            _(assume ed == addr :: low)
            if(ed == addr)
            {
                  *p = s->pub_key;
                  _(fold ar_sec(s, n; ios, prevs))
                  return Success;
            }
            else
            {
                  status_code ret = get_key_by_email(s+1, n-1, addr, p);
                  _(fold ar_sec(s, n; ios, prevs))
                  return ret; 
            }
        }
   }
 }


/* returns the email address related to public key */

status_code get_address_by_key(struct state *s, int n, public_key pubkey, email_address *p)
 _(requires exists list<struct event> ios. io_trace(;ios))
 _(requires exists list<email_address> prevs. ar_sec(s, n; ios, prevs))
 _(requires n >= 0 && n :: low)
 _(requires length_is_low(;ios))
 _(requires exists email_address vorig. p |-> vorig)
 _(ensures result :: low)
 _(ensures result == Success || result == Failure)
 _(ensures exists email_address vnew. p |-> vnew)
 _(ensures result == Failure ==> vnew == vorig)
 _(ensures  ar_sec(s, n; ios, prevs))
 _(ensures io_trace(;ios))
 _(ensures length_is_low(;ios))
 {
    
    if(n == 0)
    {
      _(unfold ar_sec(s, 0; ios, prevs))
      _(fold ar_sec(s, 0; ios, prevs))
      return Failure;

    }
    else
    {
        _(unfold ar_sec(s, n; ios, prevs))
        _(assert exists email_address adt, token tk, registration_state cc, public_key pkey. 
            &s->stored_address |-> adt && &s->stored_token |-> tk && &s->state |-> cc &&  
            &s->pub_key |-> pkey)
        _(assert cc == registration_undefined || cc == registration_initiated || cc == registration_confirmed)   
    
        registration_state st = s->state;

        
        if(st == registration_undefined)
        {
              // hopeless situation because everything is undefined after this
              _(fold ar_sec(s, n; ios, prevs))
              return Failure;
        }
        else if (st == registration_initiated)
        {
              status_code ret = get_address_by_key(s+1, n-1, pubkey, p);
              _(fold ar_sec(s, n; ios, prevs))
              return ret; 
        }
        else
        {
            _(assert st == registration_confirmed)
            public_key pbkey = s->pub_key;
            _(assume pbkey == pubkey :: low)
            
            if(pbkey == pubkey)
            {
                *p = s->stored_address;
                _(fold ar_sec(s, n; ios, prevs))
                return Success;
            }
            else
            {
                 status_code ret = get_address_by_key(s+1, n-1, pubkey, p);
                 _(fold ar_sec(s, n; ios, prevs))
                return ret;
            }
        }
    } 
 }