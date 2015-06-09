package pt.ulisboa.tecnico;

public class TestDoubleRecursion {
  public static void main(String[] args) {
    try {
      int n = cute.Cute.input.Integer();
      Fib f = (Fib) cute.Cute.input.Object("pt.ulisboa.tecnico.internal.FibImpl");
      cute.Cute.Assume(f != null);
      f.get(n);
    } catch(Throwable t) {
      t.printStackTrace();
    }
  }
}

