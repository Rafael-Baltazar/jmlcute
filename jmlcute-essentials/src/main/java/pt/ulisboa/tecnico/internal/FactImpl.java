package pt.ulisboa.tecnico.internal;

import pt.ulisboa.tecnico.Fact;

public class FactImpl implements Fact {
  public int get(int n) {
    cute.Cute.Assume(n > 0);
    if (n < 2) {
      return n;
    } else {
      return n*get(n-2);
    }
  }
}

