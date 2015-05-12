package pt.ulisboa.tecnico;

/* JUnit test case generated automatically by CUTE */
import junit.framework.*;

public class Add_execute_Test extends TestCase implements cute.Input {
    private Object[] input;
    private int i;

    public Add_execute_Test(String name){
        super(name);
    }

    public boolean Boolean() {
        return ((Boolean)input[i++]).booleanValue();
    }

    public short Short() {
        return ((Short)input[i++]).shortValue();
    }

    public int Integer() {
        return ((Integer)input[i++]).intValue();
    }

    public long Long() {
        return ((Long)input[i++]).longValue();
    }

    public float Float() {
        return ((Float)input[i++]).floatValue();
    }

    public double Double() {
        return ((Double)input[i++]).doubleValue();
    }

    public char Character() {
        return ((Character)input[i++]).charValue();
    }

    public byte Byte() {
        return ((Byte)input[i++]).byteValue();
    }

    public Object Object(String type) {
        return input[i++];
    }
    
    public Object ObjectShallow(String type) {
        return input[i++];
    }

    public void test1(){
        i=0;
        input = new Object[3];
        input[i++] = new Integer(0);
        input[i++] = new Integer(0);
        input[i++] = null;
        i=0;
        cute.Cute.input = this;
        Add.execute();
    }

    public void test2(){
        i=0;
        input = new Object[3];
        input[i++] = new Integer(0);
        input[i++] = new Integer(0);
        pt.ulisboa.tecnico.Add tmp1 = new pt.ulisboa.tecnico.Add();
        input[i++] = tmp1;
        i=0;
        cute.Cute.input = this;
        Add.execute();
    }

    public void test3(){
        i=0;
        input = new Object[3];
        input[i++] = new Integer(1);
        input[i++] = new Integer(0);
        pt.ulisboa.tecnico.Add tmp1 = new pt.ulisboa.tecnico.Add();
        input[i++] = tmp1;
        i=0;
        cute.Cute.input = this;
        Add.execute();
    }

    public void test4(){
        i=0;
        input = new Object[3];
        input[i++] = new Integer(1);
        input[i++] = new Integer(1);
        pt.ulisboa.tecnico.Add tmp1 = new pt.ulisboa.tecnico.Add();
        input[i++] = tmp1;
        i=0;
        cute.Cute.input = this;
        Add.execute();
    }

}
