package pt.ulisboa.tecnico.internal;

//Used in specifications
//@ pure
public class FibCorrectImpl {
    public int get(int n) {
        if (n < 1) {
            return 0;
        } else if (n == 1) {
            return 1;
        } else {
            return get(n - 1) + get(n - 2);
        }
    }
}
