package pt.ulisboa.tecnico;

//@import pt.ulisboa.tecnico.internal.FibCorrectImpl;

public interface Fib {
  //@ requires n >= 0;
  //@ ensures \result == new FibCorrectImpl().get(\old(n));
  int get(int n);
}

