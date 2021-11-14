/* run with -no:mod */
#include "secc.h"

/* a constant byte used to indicate when to switch modes */
_(constant int SWITCH_CMD)

#if __SECC

_(rewrites
    forall int a, int b.
        0 <= a && 0 < b && a <= b ==> a%b == a;
	forall int a, int b.
		0 <= a && 0 < b ==> (a + b)%b == a%b)

_(function list<int> snoc(int x, list<int> l))

_(rewrites
  forall int x. snoc(x,nil) == cons(x,nil);
  forall int x, int hd, list<int> tl. snoc(x,cons(hd,tl)) == cons(hd,snoc(x,tl)))

_(function list<int> append(list<int> fst, list<int> snd))

_(rewrites
  forall list<int> snd. append(nil,snd) == snd;
  forall int hd, list<int> tl, list<int> snd. append(cons(hd,tl),snd) == cons(hd,append(tl,snd)))

_(function list<int> reverse(list<int> lst))

_(rewrites
  reverse(nil) == nil;
  forall int hd, list<int> tl. reverse(cons(hd,tl)) == snoc(hd,reverse(tl)))


_(function list<int> rotate(int n,list<int> l))

_(rewrites
  forall int hd, list<int> tl, int n.
    n > 0 ==> rotate(n,cons(hd,tl)) == rotate(n-1, snoc(hd, tl));
  forall list<int> l, int n.
    n <= 0 ==> rotate(n,l) == l)

void snoc_append(int x, list<int> l)
  _(lemma)
  _(pure)
  _(ensures snoc(x,l) == append(l,cons(x,nil)))
{
  if (l == nil){
  }else{
    _(assert exists int hd, list<int> tl. l == cons(hd,tl))
    snoc_append(x,tl);
  }
}

_(predicate ar(int *a; int n, list<int> abs)
  (0 < n ==> exists int x, list<int> tl. abs == cons(x,tl) &&
             a |-> x && x == 0 && ar(a+1; n-1, tl)) &&
  (n == 0 ==> abs == nil))

/* Slice a[i%n]...a[j%n] of array a[0]...a[n] */
_(predicate slice(int *a, int i, int j; int n, sec l, list<int> abs)
  (i < j ==> exists int x, list<int> tl. abs == cons(x,tl) &&
     &a[i%n] |-> x && x :: l && (x == SWITCH_CMD) :: low && slice(a, i+1, j; n, l, tl)) &&
  (i >= j ==> abs == nil))

void slice_0(int *a, int i, int n, sec l)
    _(lemma)
   _(ensures slice(a, i, i; n, l, nil))
{
    _(fold slice(a, i, i; n, l, nil))
}

void slice_nil(int *a, int i, int n, sec l, list<int> abs)
    _(lemma)
   _(requires slice(a, i, i; n, l, abs))     
   _(ensures slice(a, i, i; n, l, abs))
   _(ensures abs == nil)
{
    _(unfold slice(a, i, i; n, l, abs))
    _(assert abs == nil)
    _(fold slice(a, i, i; n, l, nil))      
}

void slice_1(int *a, int i, int n, sec l)
    _(lemma)
    _(requires exists int x. &a[i%n] |-> x && x :: l && x == SWITCH_CMD :: low)
    _(ensures slice(a, i, i+1; n, l, cons(x,nil)))
{
    slice_0(a, i+1, n, l);
    _(fold slice(a, i, i+1; n, l, cons(x,nil)))
}

void slice_eqnil_low(int *a, int i, int j, int n, sec l, list<int> abs)
    _(lemma)
    _(requires i <= j && i :: low && j :: low)
    _(requires slice(a, i, j; n, l, abs))
    _(ensures  abs == nil :: low)
    _(ensures slice(a, i, j; n, l, abs))     
{
    _(unfold slice(a, i, j; n, l, abs))
    _(fold slice(a, i, j; n, l, abs))        
}
     
void slice_snoc(int *a, int i, int j, int n, sec l, int x, list<int> abs)
    _(lemma)
    _(requires i <= j && i :: low && j :: low)
    _(requires slice(a, i, j; n, l, abs))
    _(requires &a[j%n] |-> x && x :: l && x == SWITCH_CMD :: low)
    _(ensures  slice(a, i, j+1; n, l, snoc(x,abs)))
{
    _(unfold slice(a, i, j; n, l, abs))
    if(i < j) {
        _(assert exists int hd, list<int> tl. abs == cons(hd,tl))
        slice_snoc(a, i+1, j, n, l, x, tl);
        _(fold slice(a, i, j+1; n, l, snoc(x,abs)))
    } else {
        slice_1(a, j, n, l);
    }
}

void slice_concat(int *a, int i, int k, int j, int n, sec l,
                  list<int> fst, list<int> snd)
    _(lemma)
    _(requires i <= k && k <= j)
    _(requires i :: low && k :: low && j :: low)
    _(requires slice(a, i, k; n, l, fst))
    _(requires slice(a, k, j; n, l, snd))
    _(ensures  slice(a, i, j; n, l, append(fst,snd)))
{
    _(unfold slice(a, i, k; n, l, fst))
    if(i < k) {
        _(assert exists int hd, list<int> tl. fst == cons(hd,tl))
        slice_concat(a, i+1, k, j, n, l, tl, snd);
        _(fold slice(a, i, j; n, l, append(fst,snd)))
    }
}


void slice_high(int *a, int i, int j, int n, sec l, list<int> abs)
    _(lemma)
    _(requires i :: low && j :: low)
    _(requires slice(a, i, j; n, l, abs))
    _(ensures  slice(a, i, j; n, high, abs))
{
    _(unfold slice(a, i, j; n, l, abs))
    if(i < j) {
      _(assert exists int hd, list<int> tl. abs == cons(hd,tl))
      slice_high(a, i+1, j, n, l, tl);
    }
    _(fold slice(a, i, j; n, high, abs))
}

void slice_rotate(int *a, int i, int j, int n, sec l, list<int> abs)
    _(lemma)
    _(requires i :: low && j :: low && n :: low && 0 <= i && i <= j && 0 < n)
    _(requires slice(a, i, i+n; n, l, abs))
    _(ensures  slice(a, j, j+n; n, l, rotate(j-i,abs)))
{
   if(i < j) {
       _(unfold slice(a, i, i+n; n, l, abs))
       _(assert exists int hd, list<int> tl. abs == cons(hd,tl))
       _(assert (i+n)%n == i%n)
       slice_snoc(a, i+1, i+n, n, l, hd, tl);
       slice_rotate(a, i+1, j, n, l, snoc(hd,tl));
   }
   // Needed to apply the rotate rewrite rules   
   _(assert i >= j ==> j - i <= 0)
   _(assert i < j ==> j - i > 0)     
}

void slice_from_ar(int *a, int i, int k, int n, list<int> abs)
    _(lemma)
    _(requires ar(a + i; k, abs))
    _(requires k :: low && 0 <= i && 0 <= k && i + k <= n)
    _(ensures  slice(a, i, i + k; n, high, abs))
{
    _(unfold ar(a + i; k, abs))
    if(k != 0) {
        _(assert 0 <= i && 0 < n && i <= n) // triggers the rewrite rule
        _(assert exists int hd, list<int> tl. abs == cons(hd,tl))
        _(assert i%n == i)
        slice_from_ar(a, i+1, k-1, n, tl);
    }
    _(fold slice(a, i, i + k; n, high, abs))
}

_(function int length(list<int> l))

_(rewrites
  length(nil) == 0;
  forall int hd, list<int> tl. length(cons(hd,tl)) == length(tl) + 1)

void slice_length(int *a, int i, int j, list<int> abs)
  _(lemma) 
  _(requires exists int n, sec l. slice(a, i, j; n, l, abs))
  _(requires i <= j && i :: low && j :: low)
  _(ensures length(abs) == j - i)
  _(ensures slice(a, i, j; n, l, abs))
{

  _(unfold slice(a, i, j; n, l, abs))
  if (i < j){
    _(assert exists int hd, list<int> tl. abs == cons(hd,tl))
    slice_length(a,i+1,j,tl);
  }
  _(fold slice(a, i, j; n, l, abs))
}

void length_nonnegative(list<int> xs)
_(ensures length(xs) >= 0)
_(lemma) _(pure)
{
  if (xs == nil){
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    length_nonnegative(ys);
  }
}

void length_zero_nil(list<int> xs)
_(requires length(xs) == 0)
_(ensures xs == nil)
_(lemma) _(pure)
{
  if (xs == nil){
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
    length_nonnegative(ys);
    _(assert length(xs) > 0)
  }
}

void length_nonzero_cons(list<int> xs)
_(requires length(xs) != 0)
_(ensures exists int y, list<int> ys. xs == cons(y,ys))
_(lemma) _(pure)
{
  if (xs == nil){
    _(assert length(xs) == 0)
  }else{
    _(assert exists int y, list<int> ys. xs == cons(y,ys))
  }
}

void snoc_append2(int x, list<int> fst, list<int> snd)
  _(ensures snoc(x,append(fst,snd)) == append(fst,snoc(x,snd)))
  _(lemma)
  _(pure)
{
  if (fst != nil){
    _(assert exists int hd, list<int> tl. fst == cons(hd,tl))
    snoc_append2(x, tl, snd);
  }
}    

void append_snoc2(int hd, list<int> snd, list<int> tl)
  _(ensures append(snoc(hd,snd), tl) == append(snd,cons(hd,tl)))
  _(lemma)
  _(pure)
{
  if (snd != nil){
    _(assert exists int shd, list<int> stl. snd == cons(shd,stl))
    append_snoc2(hd, stl, tl);
  }    
}

void append_nil(list<int> lst)
  _(ensures append(lst,nil) == lst)
  _(lemma)
  _(pure)
{
  if (lst != nil){
    _(assert exists int hd, list<int> tl. lst == cons(hd,tl))
    append_nil(tl);
  }
}
  
void rotate_append(int n, list<int> fst, list<int> snd)
  _(requires n == length(fst) && n :: low && n >= 0)
  _(ensures rotate(n,append(fst,snd)) == append(snd,fst))
  _(lemma)
{
  if (n > 0){
    _(assert length(fst) :: low)        
    length_nonzero_cons(fst);

    _(assert exists int hd, list<int> tl. fst == cons(hd,tl))
    // needed to trigger rewriting of rotate
    length_nonnegative(tl);
    _(assert length(tl) + 1 > 0)

    // needed to prove length(tl) :: low
    _(assert length(tl) == length(fst) - 1)
        
    rotate_append(length(tl),tl,snoc(hd,snd));      
    append_snoc2(hd,snd,tl);
    snoc_append2(hd,tl,snd);
  }else{
    length_zero_nil(fst);
    append_nil(snd);
    _(assert 0 <= 0)
    _(assert rotate(0,snd) == snd)    
  }
}
  
#endif // __SECC

typedef struct {
    int *data;        /* the backing memory */
    int capacity;     /* Probably should be a power of two but not enforced */
    int write_index;  /* intentionally not wrapped to capacity */
    int read_index;   /* intentionally not wrapped to capacity */
} rb_t;

_(predicate rb(rb_t *buf; int *_data, int _capacity, int _write_index,
               int _read_index, sec _level, list<int> _abs, list<int> _free)
    &buf->data        |-> _data &&
    &buf->capacity    |-> _capacity &&
    &buf->write_index |-> _write_index &&
    &buf->read_index  |-> _read_index &&
   _capacity :: low && _write_index :: low && _read_index :: low &&
    0 <= _read_index && _read_index <= _write_index && 0 < _capacity &&
    _write_index <= _read_index + _capacity &&
    slice(_data, _read_index, _write_index; _capacity, _level, _abs) &&
    slice(_data, _write_index, _read_index + _capacity; _capacity, high,
          _free))

#if __SECC
void rb_high(rb_t *buf)
  _(requires exists int *_data, int _capacity, int _write_index,
    int _read_index, sec _l, list<int> _abs, list<int> _free.
    rb(buf; _data, _capacity, _write_index, _read_index, _l, _abs, _free))
  _(ensures rb(buf; _data, _capacity, _write_index, _read_index, high, _abs, _free))
  _(lemma)
{
  _(unfold rb(buf; _data, _capacity, _write_index, _read_index, _l,
              _abs, _free))
  _(apply slice_high(_data, _read_index, _write_index, _capacity, _l, _abs);)
  _(fold rb(buf; _data, _capacity, _write_index, _read_index, high,
            _abs, _free))
}
#endif // __SECC

int rb_init(rb_t *buf, int capacity, int *backing)
  _(requires exists int * _data, int _capacity, int _write_index,
      int _read_index, list<int> abs.
        &buf->data        |-> _data &&
        &buf->capacity    |-> _capacity &&
        &buf->write_index |-> _write_index &&
        &buf->read_index  |-> _read_index)
  _(requires 0 < capacity && capacity :: low)

_(requires ar(backing; capacity, abs))
  _(ensures  rb(buf; backing, capacity, 0, 0, low, nil, abs))
{
    buf->data = backing;
    buf->capacity = capacity;
    buf->write_index = 0;
    buf->read_index = 0;
    _(fold slice(backing, 0, 0; capacity, low, nil))
    _(slice_from_ar(backing, 0, capacity, capacity, abs);)
    _(fold rb(buf; backing, capacity, 0, 0, low, nil, abs))
    return 0;
}


void rb_put(rb_t * buf, int byte)
  _(requires exists int * _data, int _c, int _w, int _r, sec _l,
    list<int> _abs, list<int> _free.
    rb(buf; _data, _c, _w, _r, _l, _abs, _free))
  _(requires byte :: _l && byte == SWITCH_CMD :: low)
  
  _(ensures  exists int _new_r, list<int> _new_abs, list<int> _new_free.
    rb(buf; _data, _c, _w + 1, _new_r, _l, _new_abs, _new_free))
  _(ensures _w == _r + _c :: low && _w == _r + _c 
    ? exists int _hd, list<int> _tl. _abs == cons(_hd,_tl) &&
        _new_r == _r + 1 && _free == nil && _new_free == _free &&
        _new_abs == snoc(byte,_tl)
    : exists int _fhd, list<int> _ftl. _free == cons(_fhd,_ftl) &&
        _new_r == _r && _new_free == _ftl && _new_abs == snoc(byte,_abs))
{
  _(unfold rb(buf; _data, _c, _w, _r, _l, _abs, _free))
  if (buf->write_index == buf->read_index + buf->capacity){
    _(unfold slice(_data, _w, _r + _c; _c, high, _free))
    _(unfold slice(_data, _r, _w; _c, _l, _abs))
    _(assert exists int _hd, list<int> _tl. _abs == cons(_hd,_tl))

    int index = buf->write_index % buf->capacity;

    /* needed to prove the heap access valid */
    _(assert _w % _c == _r % _c)
    _(assert _data + (_w % _c) |-> _hd)
      
    buf->data[index] = byte;
    buf->write_index++;
    buf->read_index++;
    
    _(fold slice(_data, _r, _w; _c, _l, cons(byte,_tl)))
    _(apply slice_rotate(_data, _r, _r+1, _c, _l, cons(byte,_tl));)
    _(fold slice(_data, _w+1, _r + 1 + _c; _c, high, nil))

    /* needed to trigger rewrite for rotate */
    _(assert((_r + 1) - _r > 0) && (_r + 1) - _r - 1 <= 0)

    _(fold rb(buf; _data, _c, _w + 1, _r + 1, _l, snoc(byte,_tl), _free))
    
  }else{
    _(unfold slice(_data, _w, _r + _c; _c, high, _free))
    _(assert exists int _hd, list<int> _tl. _free == cons(_hd,_tl))
    
    int index = buf->write_index % buf->capacity;
    buf->data[index] = byte;
    buf->write_index++;
    
    _(apply slice_snoc(_data, _r, _w, _c, _l, byte, _abs);)
    _(fold rb(buf; _data, _c, _w + 1, _r, _l, snoc(byte,_abs), _tl))
   }
}

int rb_get(rb_t *buf, int *out)
  _(requires exists int *_data, int _c, int _w, int _r, sec _l,
    list<int> _abs, list<int> _free.
    rb(buf; _data, _c, _w, _r, _l, _abs, _free))
  _(requires exists int _old_out. out |-> _old_out)

  _(ensures exists int _new_r, list<int> _new_abs, list<int> _new_free.
    rb(buf; _data, _c, _w, _new_r, _l, _new_abs, _new_free))
  _(ensures _r != _w :: low && result :: low &&
            result == (_r != _w ? 0 : 1))
  _(ensures (_abs == nil :: low) && (_abs != nil ==> result == 0))
  _(ensures result == 0
    ? exists int _hd, list<int> _tl. _abs == cons(_hd,_tl) && out |-> _hd &&
    _hd :: _l && _hd == SWITCH_CMD :: low && _new_abs == _tl &&
        _new_free == snoc(_hd,_free) && _new_r == _r + 1
    : out |-> _old_out && _new_abs == _abs && _new_r == _r &&
      _new_free == _free)
{
    _(unfold rb(buf; _data, _c, _w, _r, _l, _abs, _free))
    _(apply slice_eqnil_low(_data, _r, _w, _c, _l, _abs);)
    if (buf->read_index != buf->write_index) {
        _(unfold slice(_data, _r, _w; _c, _l, _abs))
        _(assert exists int _hd, list<int> _tl. _abs == cons(_hd,_tl))
          
        int index = buf->read_index % buf->capacity;
        (*out) = ((buf->data)[index]);
        buf->read_index = buf->read_index + 1;
    	
        _(assert (_r + _c)%_c == _r%_c)
        _(assert exists int _out. out |-> _out)
        _(apply slice_snoc(_data, _w, _r+_c, _c, high, _out, _free);)
        _(fold rb(buf; _data, _c, _w, _r+1, _l, _tl, snoc(_out, _free)))
        return 0;
    } else {
        _(apply slice_nil(_data, _r, _c, _l, _abs);)
        _(fold rb(buf; _data, _c, _w, _r, _l, _abs, _free))
        return 1;
    }
}
  
void rb_clear(rb_t * buf)
    _(requires exists int * _data, int _c, int _w, int _r, sec _l,
                    list<int> _abs, list<int> _free.
      rb(buf; _data, _c, _w, _r, _l, _abs, _free))

    _(ensures rb(buf; _data, _c, _w, _w, low, nil, append(_free,_abs)))
{
    _(unfold rb(buf; _data, _c, _w, _r, _l, _abs, _free))
    buf->read_index = buf->write_index;
    _(slice_0(_data, _w, _c, low);)
    _(slice_high(_data, _r, _w, _c, _l, _abs);)
      
    _(apply slice_length(_data, _r, _w, _abs);)    
    _(slice_concat(_data, _r, _w, _r + _c, _c, high, _abs, _free);)

    _(slice_rotate(_data, _r, _w, _c, high, append(_abs, _free));)
    _(apply rotate_append(_w - _r, _abs, _free);)
    _(fold rb(buf; _data, _c, _w, _w, low, nil, append(_free, _abs)))
}


_(predicate inv(rb_t *buf, int *display_mode, int *switch_mode)
      exists int * _data, int _c, int _w, int _r, sec _l,
             list<int> _abs, list<int> _free, int _mode.
      rb(buf; _data, _c, _w, _r, _l, _abs, _free) &&
      display_mode |-> _mode && switch_mode |-> _mode &&
      _mode :: low &&
      _mode == 0 ? _l == low : _l == high)

_(predicate input_avail(int dummy))


rb_t * g_buf;

int * g_display_mode;
int * g_switch_mode;



void lock();
_(ensures inv(g_buf,g_display_mode,g_switch_mode))

void unlock();
_(requires inv(g_buf,g_display_mode,g_switch_mode))

int is_input_avail();
  _(ensures result :: low && result ==> input_avail(0))

int get_input();
  _(requires input_avail(0))
  _(requires exists int _mode. g_display_mode |-> _mode && _mode :: low)
  _(ensures g_display_mode |-> _mode)  
  _(ensures result == SWITCH_CMD :: low)
  _(ensures result :: (_mode == 0 ? low : high))
    
void input_thread()
    _(requires true)
    _(ensures true)
{
  while(1){
    lock();
    _(unfold inv(g_buf,g_display_mode,g_switch_mode))
    if (is_input_avail()){
      int byte = get_input();
      rb_put(g_buf,byte);
    }
    _(fold inv(g_buf,g_display_mode,g_switch_mode))
    unlock();
  }
}


/* use the ring buffer in a CDDC-like system */
int *g_temp;

void output_low(int byte);
_(requires byte :: low)

void output_high(int byte);
_(requires byte :: high)

int SWITCH_CMD;

void random_delay();
  _(requires true)
  _(ensures true)

// callback to be called when the display mode is updated
void display_mode_updated();
  _(requires exists int _mode. g_display_mode |-> _mode)
  _(ensures g_display_mode |-> _mode)

void output_thread()
  _(requires exists int _t. g_temp |-> _t)
  _(ensures exists int _t. g_temp |-> _t)
{
  while(1)
    _(invariant exists int _t. g_temp |-> _t)
  {
    random_delay(); // add in a random delay to simulate jitter
    lock();
    _(unfold inv(g_buf,g_display_mode,g_switch_mode))
    if (rb_get(g_buf,g_temp) == 0){
      if (*g_temp == SWITCH_CMD){
        // switch domains
        if (*g_switch_mode == 0){
          *g_switch_mode = 1;
          *g_display_mode = 1;
          display_mode_updated();
          rb_clear(g_buf);
          _(apply rb_high(g_buf);)
        }else{
          *g_switch_mode = 0;
          *g_display_mode = 0;
          display_mode_updated();          
          rb_clear(g_buf);
        }
      }else{
        if (*g_switch_mode == 0){
          output_low(*g_temp);
        }else{
          output_high(*g_temp);
        }
      }
    }
    _(fold inv(g_buf,g_display_mode,g_switch_mode))      
    unlock();
  }
}
