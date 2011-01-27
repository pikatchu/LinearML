#include<malloc.h>
#include<string.h>

typedef struct{
  int size ;
  char* value ;
} string_t ;

string_t* string_make(char* v){
  int size = strlen(v) + 1 ;
  string_t* s ; 
  s = malloc(sizeof(string_t)) ;
  s->size = size ;
  s->value = malloc(size) ;
  strcpy(s->value, v) ;
  return s ;
}

void string_release(string_t* s){
  free(s->value) ;
  free(s) ;
  return ;
}

int string_length(string_t* s){
  return (s->size - 1) ;
}
