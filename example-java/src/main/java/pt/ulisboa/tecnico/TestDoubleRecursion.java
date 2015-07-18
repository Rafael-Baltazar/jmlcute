package pt.ulisboa.tecnico;

import cute.Cute;

public class TestDoubleRecursion {
    public static void main(String[] args) {
        pt.ulisboa.tecnico.internal.FibImpl receiver = (pt.ulisboa.tecnico.internal.FibImpl) Cute.input.Object("pt.ulisboa.tecnico.internal.FibImpl");
        cute.Cute.Assume(receiver != null);
        int arg0 = cute.Cute.input.Integer();
        receiver.get(arg0);
    }
}
