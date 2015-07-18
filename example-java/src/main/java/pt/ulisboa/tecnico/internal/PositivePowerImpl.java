package pt.ulisboa.tecnico.internal;

import pt.ulisboa.tecnico.PositivePower;
//@ import pt.ulisboa.tecnico.internal.PositivePowerCorrectImpl;

public class PositivePowerImpl implements PositivePower {
    //@ requires p >= 0;
    //@ ensures \result/res == new PositivePowerCorrectImpl().get(\old(n),\old(p));
    private int get(int n, int p, int res) {
        if (p == 1) {
            return res;
        } else {
            return get(n, p - 1, res * n);
        }
    }

    public int get(int n, int p) {
        return get(n, p, 1);
    }
}

