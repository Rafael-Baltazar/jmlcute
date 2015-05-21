package pt.ulisboa.tecnico;

public class Run {
  /*@
    @ requires o == null;
    @ assignable \nothing;
    @ signals (NullPointerException e) \old(o) == null;
   @*/
  public static void isNull(Object o) {
    if (o == null) {
      throw new NullPointerException();
    }
  }

  public static void main(String[] args) {
    try {
      int x = cute.Cute.input.Integer();
      Fib a = ((Fib) cute.Cute.input.Object("pt.ulisboa.tecnico.internal.FibMemoized"));
      a.get(x);
    } catch(Throwable t) {
      t.printStackTrace();
    }
  }
}

