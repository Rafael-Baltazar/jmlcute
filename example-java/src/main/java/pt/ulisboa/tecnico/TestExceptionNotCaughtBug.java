package pt.ulisboa.tecnico;

public class TestExceptionNotCaughtBug {
  /*@
    @ requires o == null;
    @ assignable \nothing;
    @ signals (DefinitelyNotNullPointerException e) \old(o) == null;
   @*/
  public static void isNull(Object o) throws DefinitelyNotNullPointerException {
    if (o == null) {
      throw new DefinitelyNotNullPointerException();
    }
  }

  public static void main(String[] args) {
    try {
      isNull(null);
    } catch(Throwable t) {
      t.printStackTrace();
    }
  }

  private static class DefinitelyNotNullPointerException extends Exception {}
}

