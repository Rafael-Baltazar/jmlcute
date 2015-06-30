package pt.ulisboa.tecnico;

public class TestLinearArithmetic {
  public static void main(String[] args) {
    try {
      int n = cute.Cute.input.Integer();
      int y = cute.Cute.input.Integer();
      cute.Cute.Assert(n > -2);
      cute.Cute.Assert(y > n);
    } catch(Throwable t) {
      t.printStackTrace();
    }
  }
}
