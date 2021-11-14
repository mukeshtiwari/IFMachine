#include "secc.h"

int encrypt(int *dst, int *src, int *key)
  _(requires exists int dstv. dst |-> dstv)
  _(requires exists int srcv. src |-> srcv && srcv :: high())
  _(requires exists int keyv. key |-> keyv && keyv :: high())
  _(ensures  exists int dstvnew. result :: low() && dst |-> dstvnew && dstvnew :: (result == 0 ? low() : high()))
  _(ensures src |-> srcv && srcv :: high() && key |-> keyv && keyv :: high())
{
  *dst = *src + *key;
  /* pretend that this is secure encryption */
  _(assert exists int dstvnew. dst |-> dstvnew)
  _(assume dstvnew :: low())
  return 0;
}

int decrypt(int *dst, int *src, int *key)
  _(requires exists int dstv. dst |-> dstv)
  _(requires exists int srcv. src |-> srcv && srcv :: low())
  _(requires exists int keyv. key |-> keyv && keyv :: high())
  _(ensures  exists int dstvnew. result :: low() && dst |-> dstvnew && dstvnew :: (result == 0 ? high() : low()))
  _(ensures src |-> srcv && srcv :: low() && key |-> keyv && keyv :: high())
{
  *dst = *src - *key;
  return 0;
}
  

int *alloc();
_(ensures exists int v. result |-> v)

void free(int *p);
_(requires exists int v. p |-> v)

int * secure(int *plaintext, int *key)
_(requires exists int pv. plaintext |-> pv)
_(requires exists int keyv. key |-> keyv)
_(ensures  exists int v. result |-> v && v :: low())
{
  int *ciphertext = alloc();
  int res = encrypt(ciphertext,plaintext,key);
  if (res != 0){
    /* encryption failed so zero ciphertext to ensure no leakage */
    *ciphertext = 0;
  }else{
    int * pcopy = alloc();
    *pcopy = *plaintext;
    _(assert exists int pvcopy. pcopy |-> pvcopy && pvcopy :: high())
    if (decrypt(pcopy,ciphertext,key) != 0){
      /* decrytion failed, so releasing the supposed plaintext is OK */
      *ciphertext = *pcopy;
    }
    free(pcopy);
  }
  free(plaintext);
  free(key);
  return ciphertext;
}

