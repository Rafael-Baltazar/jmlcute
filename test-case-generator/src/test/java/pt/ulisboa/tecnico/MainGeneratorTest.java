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
     * Test samplePackageName.SampleClassName with a public method app and
     * several non-public non-instance methods.
     */
    public void testSampleClassName() {
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
                .equals("jmlcute__samplePackageName__SampleClassName__app_samplePackageName__SampleClassName_int.java"));
        StringBuilder sb = new StringBuilder();
        sb.append("package samplePackageName;\n");
        sb.append("\n");
        sb.append("public class jmlcute__samplePackageName__SampleClassName__app_samplePackageName__SampleClassName_int {\n");
        sb.append("  public static void main(String[] args) {\n");
        sb.append("    samplePackageName.SampleClassName receiver = (samplePackageName.SampleClassName) cute.Cute.input.Object(\"samplePackageName.SampleClassName\");\n");
        sb.append("    cute.Cute.Assume(receiver != null);\n");
        sb.append("    samplePackageName.SampleClassName arg0 = (samplePackageName.SampleClassName) cute.Cute.input.Object(\"samplePackageName.SampleClassName\");\n");
        sb.append("    int arg1 = (int) cute.Cute.input.Integer();\n");
        sb.append("    receiver.app(arg0, arg1);\n");
        sb.append("  }\n");
        sb.append("}\n");
        assertTrue("The MainClass is incorrect.", sb.toString().equals(
                mainClasses[0].getJavaFile().toString()));
    }

    /**
     * Test samplePackageName.SampleSuperclassName with two public methods
     * (superclassApp and superclassThrows).
     */
    public void testSampleSuperclassName() {
        MainGenerator mainGenerator = new MainGenerator();
        MainClass[] mainClasses = new MainClass[0];
        try {
            mainClasses = mainGenerator.generate(
                    "samplePackageName.SampleSuperclassName");
        } catch (ClassNotFoundException e) {
            fail("samplePackageName.SampleSuperclassName was not found.");
        }
        assertTrue("mainClasses is of incorrect size.", mainClasses.length == 2);
        String zeroDirectoryName = mainClasses[0].getDirectoryName(),
                oneDirectoryName = mainClasses[1].getDirectoryName();
        assertTrue("First directory name is incorrect.",
                zeroDirectoryName.equals("samplePackageName"));
        assertTrue("Second directory name is incorrect.",
                oneDirectoryName.equals("samplePackageName"));
        String zeroFileName = mainClasses[0].getFileName();
        String oneFileName = mainClasses[1].getFileName();
        StringBuilder sbApp = new StringBuilder();
        sbApp.append("package samplePackageName;\n");
        sbApp.append("\n");
        sbApp.append("public class jmlcute__samplePackageName__" +
                "SampleSuperclassName__superclassApp {\n");
        sbApp.append("  public static void main(String[] args) {\n");
        sbApp.append("    samplePackageName.SampleSuperclassName receiver = " +
                "(samplePackageName.SampleSuperclassName) cute.Cute.input.Object" +
                "(\"samplePackageName.SampleSuperclassName\");\n");
        sbApp.append("    cute.Cute.Assume(receiver != null);\n");
        sbApp.append("    receiver.superclassApp();\n");
        sbApp.append("  }\n");
        sbApp.append("}\n");
        StringBuilder sbThrows = new StringBuilder();
        sbThrows.append("package samplePackageName;\n");
        sbThrows.append("\n");
        sbThrows.append("public class jmlcute__samplePackageName__" +
                "SampleSuperclassName__superclassThrows {\n");
        sbThrows.append("  public static void main(String[] args) throws " +
                "java.lang.Exception {\n");
        sbThrows.append("    samplePackageName.SampleSuperclassName receiver" +
                " = (samplePackageName.SampleSuperclassName) cute.Cute.input" +
                ".Object(\"samplePackageName.SampleSuperclassName\");\n");
        sbThrows.append("    cute.Cute.Assume(receiver != null);\n");
        sbThrows.append("    receiver.superclassThrows();\n");
        sbThrows.append("  }\n");
        sbThrows.append("}\n");
        final boolean zeroIsAppFileName = zeroFileName.equals("jmlcute__" +
                "samplePackageName__SampleSuperclassName__superclassApp.java"),
                zeroIsThrowsFileName = zeroFileName.equals("jmlcute__" +
                        "samplePackageName__SampleSuperclassName__" +
                        "superclassThrows.java"),
                oneIsAppFileName = oneFileName.equals("jmlcute__" +
                        "samplePackageName__SampleSuperclassName__" +
                        "superclassApp.java"),
                oneIsThrowsFileName = oneFileName.equals("jmlcute__" +
                        "samplePackageName__SampleSuperclassName__" +
                        "superclassThrows.java");
        if (zeroIsAppFileName) {
            assertTrue("The second file name is incorrect.", oneIsThrowsFileName);
        } else {
            assertTrue("The first file name is incorrect.", zeroIsThrowsFileName);
            assertTrue("The second file name is incorrect.", oneIsAppFileName);
        }
        final boolean zeroIsAppFile = mainClasses[0].getJavaFile().toString()
                .equals(sbApp.toString()),
                zeroIsThrowsFile = mainClasses[0].getJavaFile().toString()
                        .equals(sbThrows.toString()),
                oneIsAppFile = mainClasses[1].getJavaFile().toString()
                        .equals(sbApp.toString()),
                oneIsThrowsFile = mainClasses[1].getJavaFile().toString()
                        .equals(sbThrows.toString());
        if (zeroIsAppFile) {
            assertTrue("The second MainClass is incorrect.", oneIsThrowsFile);
        } else {
            assertTrue("The first MainClass is incorrect.", zeroIsThrowsFile);
            assertTrue("The second MainClass is incorrect.", oneIsAppFile);
        }
    }
}
