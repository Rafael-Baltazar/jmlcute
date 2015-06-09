package pt.ulisboa.tecnico.internal;

import pt.ulisboa.tecnico.PositivePower;

public class PositivePowerImpl implements PositivePower {
  public int get(int n, int p) {
    if(p == 1) {
      return 1;
    } else {
      return n*get(n, p-1);
    }
  }
}

