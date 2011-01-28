#include<malloc.h>

typedef struct{
  int size ;
  void** t ;
} array_t ;

typedef struct{
  array_t *t ;
  void* v ;
} get_return_t ;

array_t* array_make(int size){
  void** t = malloc(sizeof(void*) * size) ;
  array_t *res = malloc (sizeof(array_t)) ;
  res->size = size ;
  res->t = t ;
  return res ;
}

array_t* array_set(array_t *t, int n, void* v){
  if(n < 0 || n >= t->size)
    return t ;
  t->t[n] = v ;
  return t ;
}

void* array_get(array_t *t, int n){
  if( n < 0 || n >= t->size)
    return NULL ;

  void* res ;
  res = t->t[n] ;
  t->t[n] = NULL ;
  return res ;
}

void* array_swap(array_t *t, int n, void* v){
  if( n < 0 || n >= t->size)
    return NULL ;

  void* res ;
  res = t->t[n] ;
  t->t[n] = v ;
  return res ;
}


void array_free(array_t* t, void (*free_v)(void*)){
  void** h = t->t ;
  int i ;
  for (i = 0 ; i < t->size ; i++){
    free_v(h[i]) ;
  }
  free(h) ;
  free(t) ;
}

void* array_fold_left(void* (*f)(void*, array_t*), void* acc, array_t* t){
  int i ;
  for (i = 0 ; i < t->size ; i++){
    acc = f(acc, t->t[i]) ;
  }
  free(t) ;
  return acc ;
}

typedef struct{
  int size ;
  double* t ;
} farray_t ;

farray_t* farray_make(int size, double d){
  farray_t* res ;
  int i ;
  res = malloc(sizeof(farray_t)) ;
  res->size = size ;
  res->t = malloc(sizeof(double) * size) ;
  for (i = 0 ; i < size ; i++){
    res->t[i] = d ;
  }
  return res ;
}

farray_t* farray_set(farray_t* t, int i, double v){
  if(i < 0 || i >= t->size)
    return t ;
  t->t[i] = v ;
  return t ;
}

double farray_get(farray_t* t, int i){
  if(i < 0 || i >= t->size)
    return 0.0 ;
  return t->t[i] ;
}

void farray_release(farray_t* t){
  free(t->t) ;
  free(t) ;
  return ;
}

int farray_length(farray_t* t){
  return t->size ;
}

typedef struct{
  int size ;
  int* t ;
} iarray_t ;

iarray_t* iarray_make(int size, int d){
  iarray_t* res ;
  int i ;
  res = malloc(sizeof(iarray_t)) ;
  res->size = size ;
  res->t = malloc(sizeof(int) * size) ;
  for (i = 0 ; i < size ; i++){
    res->t[i] = d ;
  }
  return res ;
}

iarray_t* iarray_set(iarray_t* t, int i, int v){
  if(i < 0 || i >= t->size)
    return t ;
  t->t[i] = v ;
  return t ;
}

int iarray_get(iarray_t* t, int i){
  if(i < 0 || i >= t->size)
    return 0 ;
  return t->t[i] ;
}

void iarray_release(iarray_t* t){
  free(t->t) ;
  free(t) ;
  return ;
}

int iarray_length(iarray_t* t){
  return t->size ;
}

iarray_t* iarray_copy(iarray_t* t){
  iarray_t* res ;
  int i ;

  res = malloc(sizeof(iarray_t)) ;
  res->size = t->size ;
  res->t = malloc(sizeof(int) * res->size) ;
  
  for(i = 0 ; i < t->size ; i++)
    res->t[i] = t->t[i] ;
  
  return res ;
}
