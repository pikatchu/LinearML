#include<pthread.h>
#include<stdlib.h>
#include<stdio.h>

typedef struct{
  void* v ;
  pthread_mutex_t m ;
  pthread_cond_t c ;
} future ;

typedef struct{
  void* (*f)(void*) ;
  void* args ;
  future* res ;
} cont ;

void* call(void* k_arg){
  cont* k = (cont*)k_arg ;
  future* res = k->res ;
  void* (*f)(void*) = k->f ;
  void* args = k-> args ;
  free(k) ;
  pthread_mutex_lock(&(res->m)) ;
  res->v = f(args) ;
  pthread_cond_signal(&(res->c)) ;
  pthread_mutex_unlock(&(res->m)) ;
}

future* spawn(void* (*f)(void*), void* args){
  pthread_t thread ;
  cont* k = malloc (sizeof(cont));
  future* res = malloc(sizeof(future)) ;

  k->f = f ;
  k->args = args ;
  k->res = res ;
  res->v = NULL ;
  pthread_mutex_init(&(res->m), NULL) ;
  pthread_cond_init(&(res->c), NULL) ;
  pthread_create(&thread, NULL, call, k);

  return res ;
}

void* mwait(future* t){
  void* res ;
  pthread_mutex_lock(&(t->m)) ;
  while(t->v == NULL){
    pthread_cond_wait(&(t->c), &(t->m)) ;
  }
  res = t->v ;
  pthread_mutex_unlock(&(t->m)) ;
  free(t) ;
  return res ;
}

void* try_get(future* t){
  void *res = t-> v ;
  return res ;
}

int is_ready(future* t){
  return (t->v != NULL) ;
}

void print_int(int x){
  printf("%d\n", x) ;
}

void print_float(float x){
  printf("%f\n", x) ;
}

int f(int x){ return x+1 ; }

