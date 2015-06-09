package pt.ulisboa.tecnico;

public interface Fact {
  //@ requires n >= 0;
  int get(int n);
}

