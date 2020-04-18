#include <stdio.h>

int main(){
  int result;
  int x = 5;
  int y = 10;
  int z;

  x = x * 2;
  z = x - y;
  result = x + y + z;

  printf("%d\n",result);
  
  return 0;
}
