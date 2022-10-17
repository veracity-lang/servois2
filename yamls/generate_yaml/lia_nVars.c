void main(int args, char** argv) {
  // ex for 5 variables
  int a, b, x0, x1, x2, x3, x4;

  // sum:
  a = a + b ;
  
  // multiVarCondSum
  if (a > 0 && x0 > x1 && x1 > x2 && x2 > x3 && x3 > x4) { 
    a = a + x4; 
  } 
  else { 
    a = x4 - a; 
  }
}
