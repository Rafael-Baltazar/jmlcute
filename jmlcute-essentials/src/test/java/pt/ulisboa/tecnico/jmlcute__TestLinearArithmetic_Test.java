package pt.ulisboa.tecnico;

/* JUnit test case generated automatically by CUTE */
import junit.framework.*;

public class jmlcute__TestLinearArithmetic_Test extends TestCase implements cute.Input {
    private Object[] input;
    private int i;

    public jmlcute__TestLinearArithmetic_Test(String name){
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

    public void test3(){
        i=0;
        input = new Object[2];
        input[i++] = new Integer(-2);
        input[i++] = new Integer(1);
        i=0;
        cute.Cute.input = this;
        TestLinearArithmetic.main(null);
    }

}
