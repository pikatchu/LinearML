#include "liml.h"

#include <stdlib.h>

typedef struct{
  lvalue counter ;
  lvalue value ;
} share_t ;

lvalue share_make(lvalue value){
  share_t *res = malloc(sizeof(share_t)) ;
  res->counter = 1 ;
  res->value = value ;
  return (lvalue) res ;
}

lvalue share_clone(lvalue v_){
  share_t *x = (share_t *)v_ ;
  __sync_fetch_and_add(&x->counter, 1) ;
  return (lvalue) x ;
}

lvalue share_release(lvalue v_){
  share_t *x = (share_t *)v_ ;
  if (x->counter == 1){
    lvalue *res = malloc(sizeof(lvalue));
    *res = x->value ;
    free(x) ;
    
    return (lvalue)res ;
  }
  
  __sync_fetch_and_sub(&x->counter, 1) ;
  return (lvalue) NONE ;
}

lvalue share_visit(share_t* x){
  return (lvalue) x->value ;
}
