#include"liml.h"
#include<math.h>

lvalue liml_sqrt(lvalue arg){
  float res = sqrt(V2F(arg)) ; 
  return F2V(res) ;
}

lvalue liml_sin(lvalue arg){
  float res = sin(V2F(arg)) ; 
  return F2V(res) ;

}
