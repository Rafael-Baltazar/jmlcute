package pt.ulisboa.tecnico;

public class Run {
  public static void main(String[] args) {
    int x = cute.Cute.input.Integer();
    int y = cute.Cute.input.Integer();
    Add a = ((Add) cute.Cute.input.Object("pt.ulisboa.tecnico.Add"));
    cute.Cute.Assume(a != null && x > 0 && y > 0);
    int res = a.execute(x,y);
    cute.Cute.Assert(res == x + y);
  }
}

