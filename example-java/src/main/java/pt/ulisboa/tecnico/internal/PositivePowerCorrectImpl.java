package pt.ulisboa.tecnico.internal;

// Used in specifications.
//@ pure
public class PositivePowerCorrectImpl {
    private int get(int n, int p, int res) {
        if (p == 0) {
            return res;
        } else {
            return get(n, p - 1, n * res);
        }
    }

    public int get(int n, int p) {
        return get(n, p, 1);
    }
}

