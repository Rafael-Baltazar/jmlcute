package pt.ulisboa.tecnico.internal;

import pt.ulisboa.tecnico.Fib;

public class FibImpl implements Fib {
  public int get(int n) {
    if(n<1) {
      return 0;
    } else if(n==1) {
      return 1;
    } else {
      return get(n-1)+get(n-3);
    }
  }
}

