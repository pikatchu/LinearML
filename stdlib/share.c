#include "liml.h"

#include <stdlib.h>

typedef struct{
  lvalue counter ;
  void* value ;
} share_t ;

share_t* share_make(void* value){
  share_t *res = malloc(sizeof(share_t)) ;
  res->counter = 1 ;
  res->value = value ;
  return res ;
}

share_t* share_clone(share_t* x){
  __sync_fetch_and_add(&x->counter, 1) ;
  return x ;
}

void** share_release(share_t* x){
  __sync_fetch_and_sub(&x->counter, 1) ;
  if (x->counter == 1){
    void** res = malloc(sizeof(lvalue));
    *res = x->value ;
    return res ;
  }
  return NULL ;
}

void* share_visit(share_t* x){
  return x->value ;
}
