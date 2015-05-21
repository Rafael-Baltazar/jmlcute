package pt.ulisboa.tecnico;

public class Add {
  //@ ensures \result == \old(x) + \old(y);
  public int execute(int x, int y) {
    return x - y;
  }
}

