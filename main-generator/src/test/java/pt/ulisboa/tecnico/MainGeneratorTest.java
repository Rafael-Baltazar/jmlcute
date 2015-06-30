package pt.ulisboa.tecnico;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple MainGeneratorApp.
 */
public class MainGeneratorTest extends TestCase {
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public MainGeneratorTest(String testName) {
        super(testName);
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite() {
        return new TestSuite(MainGeneratorTest.class);
    }

    /**
     * Test App.
     */
    public void testApp() {
        MainGenerator mainGenerator = new MainGenerator();
        StringBuilder[] stringBuilders = new StringBuilder[0];
        try {
            stringBuilders = mainGenerator.generate("App.App");
        } catch (ClassNotFoundException e) {
            fail("App.App was not found.");
        }
        assertTrue("stringBuilders is of incorrect size.", stringBuilders
                .length == 1);
        StringBuilder sb = new StringBuilder();
        sb.append("package App;\n");
        sb.append("\n");
        sb.append("public class jmlcute__App__App__app_App_App {\n");
        sb.append("  public static void main(String[] args) {\n");
        sb.append("    App.App receiver = cute.Cute.input.Object(\"\");\n");
        sb.append("    cute.Cute.Assume(receiver != null);\n");
        sb.append("    App.App arg0 = cute.Cute.input.Object(\"App.App\");\n");
        sb.append("    App.App arg1 = cute.Cute.input.Object(\"App.App\");\n");
        sb.append("    receiver.app(arg0, arg1);\n");
        sb.append("  }\n");
        sb.append("}\n");
        assertTrue("stringBuilders[0] is incorrect.", sb.toString().equals(stringBuilders[0].toString()));
    }
}
