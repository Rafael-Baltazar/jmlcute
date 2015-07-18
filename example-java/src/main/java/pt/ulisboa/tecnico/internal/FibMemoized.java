package pt.ulisboa.tecnico.internal;

import java.util.Map;
import java.util.TreeMap;
import pt.ulisboa.tecnico.Fib;

public class FibMemoized implements Fib {
  //@ private invariant memory != null && memory.size() > 1;
  private Map<Integer,Integer> memory = new TreeMap<Integer,Integer>();

  public FibMemoized() {
    memory.put(0,0);
    memory.put(1,1);
  }

  public int get(int n) {
    boolean memorized = memory.containsKey(n);
    if (memorized) {
      return memory.get(n);
    } else {
      int result = get(n-1)+get(n-2);
      memory.put(n,result);
      return result;
    }
  }
}

