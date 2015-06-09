package pt.ulisboa.tecnico;

//@ import pt.ulisboa.tecnico.internal.PositivePowerCorrectImpl;

public interface PositivePower {
  /*@
   @ requires p >= 0;
   @ ensures \old(p) >= 0;
   @ pure
   @*/
  int get(int n, int p);
}

