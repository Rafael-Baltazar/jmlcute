package pt.ulisboa.tecnico;

import pt.ulisboa.tecnico.internal.PositivePowerImpl;

public class TestRecursion {
  public static void main(String[] args) {
    try {
      int n = cute.Cute.input.Integer();
      int p = cute.Cute.input.Integer();
      PositivePower f = new PositivePowerImpl();
      cute.Cute.Assume(n < 4 && p < 4);
      f.get(n,p);
    } catch(Throwable t) {
      t.printStackTrace();
    }
  }
}

