package pt.ulisboa.tecnico;

public class Add {
  //@ requires x > 0 && y > 0;
  //@ ensures \result == \old(x) + \old(y);
  public int execute(int x, int y) {
    return x - y;
  }
}

