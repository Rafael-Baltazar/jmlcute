package pt.ulisboa.tecnico;

public class Add {
  //@ requires x > 0 && y > 0;
  public int execute(int x, int y) {
    return x - y;
  }
}

