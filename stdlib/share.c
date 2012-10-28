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
  __sync_fetch_and_sub(&x->counter, 1) ;
  if (x->counter == 1){
    lvalue *res = malloc(sizeof(lvalue));
    *res = x->value ;
    free(x) ;
    return res ;
  }
  // Option.None machine representation is 1
  return (lvalue) 1 ;
}

void* share_visit(share_t* x){
  return x->value ;
}
