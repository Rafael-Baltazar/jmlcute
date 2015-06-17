package pt.ulisboa.tecnico;

import pt.ulisboa.tecnico.internal.FibImpl;

public class TestDoubleRecursion {
    public static void main(String[] args) {
        try {
            int n = cute.Cute.input.Integer();
            cute.Cute.Assume(n >= 0 && n < 5);
            Fib f = new FibImpl();
            f.get(n);
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }
}
