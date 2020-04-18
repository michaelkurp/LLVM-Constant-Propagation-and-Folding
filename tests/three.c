#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv){
  
  int result;
 int x = atoi(argv[1]);
  int y = 6;
  int z = 3;

  x = x * 2;
  z = z - y;
result = x + y + z; //fails
//result = y + z + x; //works
//result = z + y + x; //works
//result = y + x + z; //fails
//result = z + x + y; //fails
//result = x + z + y; //fails
  printf("%d\n",result);

  return 0;
}
