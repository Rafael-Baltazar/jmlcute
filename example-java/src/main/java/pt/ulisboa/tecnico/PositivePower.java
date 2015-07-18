package pt.ulisboa.tecnico;

//@ import pt.ulisboa.tecnico.internal.PositivePowerCorrectImpl;

public interface PositivePower {
    //@ requires p >= 0;
    //@ ensures \result == new PositivePowerCorrectImpl().get(\old(n),\old(p));
    //@ pure
    int get(int n, int p);
}

