package pt.ulisboa.tecnico;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple TestCaseGeneratorApp.
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
     * Test samplePackageName with a public method app and several non-public non-instance methods.
     */
    public void testApp() {
        MainGenerator mainGenerator = new MainGenerator();
        MainClass[] mainClasses = new MainClass[0];
        try {
            mainClasses = mainGenerator.generate("samplePackageName.SampleClassName");
        } catch (ClassNotFoundException e) {
            fail("samplePackageName.SampleClassName was not found.");
        }
        assertTrue("mainClasses is of incorrect size.", mainClasses.length == 1);
        String directoryName = mainClasses[0].getDirectoryName();
        assertTrue("Directory name is incorrect.", directoryName.equals("samplePackageName"));
        String fileName = mainClasses[0].getFileName();
        assertTrue("File name is incorrect.", fileName
                .equals("jmlcute__samplePackageName__SampleClassName__app_samplePackageName__SampleClassName_samplePackageName__SampleClassName.java"));
        StringBuilder sb = new StringBuilder();
        sb.append("package samplePackageName;\n");
        sb.append("\n");
        sb.append("public class jmlcute__samplePackageName__SampleClassName__app_samplePackageName__SampleClassName_samplePackageName__SampleClassName {\n");
        sb.append("  public static void main(String[] args) {\n");
        sb.append("    samplePackageName.SampleClassName receiver = (samplePackageName.SampleClassName) cute.Cute.input.Object(\"samplePackageName.SampleClassName\");\n");
        sb.append("    cute.Cute.Assume(receiver != null);\n");
        sb.append("    samplePackageName.SampleClassName arg0 = (samplePackageName.SampleClassName) cute.Cute.input.Object(\"samplePackageName.SampleClassName\");\n");
        sb.append("    samplePackageName.SampleClassName arg1 = (samplePackageName.SampleClassName) cute.Cute.input.Object(\"samplePackageName.SampleClassName\");\n");
        sb.append("    receiver.app(arg0, arg1);\n");
        sb.append("  }\n");
        sb.append("}\n");
        assertTrue("The MainClass is incorrect.", sb.toString().equals(
                mainClasses[0].getJavaFile().toString()));
    }
}
