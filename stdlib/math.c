#include"liml.h"
#include<math.h>

lfloat liml_sqrt(lfloat arg){
  float res = sqrt(V2F(arg)) ; 
  return F2V(res) ;
}

lfloat liml_sin(int arg){
  float res = sin(V2F(arg)) ; 
  return F2V(res) ;

}
