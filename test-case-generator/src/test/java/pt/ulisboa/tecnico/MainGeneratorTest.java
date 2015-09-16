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
        assertTrue("File name is incorrect.", fileName.equals("jmlcute1.java"));
        StringBuilder sb = new StringBuilder();
        sb.append("package samplePackageName;\n");
        sb.append("\n");
        sb.append("public class jmlcute1 {\n");
        sb.append("  public static void main(String[] args) throws Throwable {\n");
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
        final MainGenerator mainGenerator = new MainGenerator();
        MainClass[] mainClasses = new MainClass[0];
        try {
            mainClasses = mainGenerator.generate(
                    "samplePackageName.SampleSuperclassName");
        } catch (ClassNotFoundException e) {
            fail("samplePackageName.SampleSuperclassName was not found.");
        }
        assertTrue("mainClasses is of incorrect size.", mainClasses.length == 2);
        final String firstDirectoryName = mainClasses[0].getDirectoryName();
        final String secondDirectoryName = mainClasses[1].getDirectoryName();
        assertTrue("First directory name is incorrect.",
                firstDirectoryName.equals("samplePackageName"));
        assertTrue("Second directory name is incorrect.",
                secondDirectoryName.equals("samplePackageName"));
        final String firstName = mainClasses[0].getFileName();
        final String firstFile = mainClasses[0].getJavaFile().toString();
        final String secondName = mainClasses[1].getFileName();
        final String secondFile = mainClasses[1].getJavaFile().toString();
        final String oneName = "jmlcute1.java";
        final String oneAppFile = createAppFile("jmlcute1").toString();
        final String oneThrowsFile = createThrowsFile("jmlcute1").toString();
        final String twoName = "jmlcute2.java";
        final String twoAppFile = createAppFile("jmlcute2").toString();
        final String twoThrowsFile = createThrowsFile("jmlcute2").toString();
        final boolean firstIsOneName = firstName.equals(oneName);
        if (firstIsOneName) {
            assertEquals("Incorrect file name.", twoName, secondName);
        } else {
            assertEquals("Incorrect file name.", twoName, firstName);
            assertEquals("Incorrect file name.", oneName, secondName);
        }
        final boolean firstIsOneAppFile = firstFile.equals(oneAppFile);
        final boolean firstIsOneThrowsFile = firstFile.equals(oneThrowsFile);
        final boolean firstIsTwoAppFile = firstFile.equals(twoAppFile);
        final boolean firstIsTwoThrowsFile = firstFile.equals(twoThrowsFile);
        final boolean secondIsOneAppFile = secondFile.equals(oneAppFile);
        final boolean secondIsOneThrowsFile = secondFile.equals(oneThrowsFile);
        final boolean secondIsTwoAppFile = secondFile.equals(twoAppFile);
        final boolean secondIsTwoThrowsFile = secondFile.equals(twoThrowsFile);
        if (firstIsOneName) {
            if (firstIsOneAppFile) {
                assertTrue("Incorrect java file.", secondIsTwoThrowsFile);
            } else {
                assertTrue("Incorrect java file.", firstIsOneThrowsFile
                        && secondIsTwoAppFile);
            }
        } else {
            if (firstIsTwoAppFile) {
                assertTrue("Incorrect java file.", secondIsOneThrowsFile);
            } else {
                assertTrue("Incorrect java file.", firstIsTwoThrowsFile
                        && secondIsOneAppFile);
            }
        }
    }

    private StringBuilder createAppFile(final String classname) {
        final StringBuilder sbApp = new StringBuilder("");
        sbApp.append("package samplePackageName;\n");
        sbApp.append("\n");
        sbApp.append("public class ").append(classname).append(" {\n");
        sbApp.append("  public static void main(String[] args) throws Throwable {\n");
        sbApp.append("    samplePackageName.SampleSuperclassName receiver = " +
                "(samplePackageName.SampleSuperclassName) cute.Cute.input.Object" +
                "(\"samplePackageName.SampleSuperclassName\");\n");
        sbApp.append("    cute.Cute.Assume(receiver != null);\n");
        sbApp.append("    receiver.superclassApp();\n");
        sbApp.append("  }\n");
        sbApp.append("}\n");
        return sbApp;
    }

    private StringBuilder createThrowsFile(final String classname) {
        StringBuilder sbThrows = new StringBuilder("");
        sbThrows.append("package samplePackageName;\n");
        sbThrows.append("\n");
        sbThrows.append("public class ").append(classname).append(" {\n");
        sbThrows.append("  public static void main(String[] args) throws Throwable {\n");
        sbThrows.append("    samplePackageName.SampleSuperclassName receiver" +
                " = (samplePackageName.SampleSuperclassName) cute.Cute.input" +
                ".Object(\"samplePackageName.SampleSuperclassName\");\n");
        sbThrows.append("    cute.Cute.Assume(receiver != null);\n");
        sbThrows.append("    receiver.superclassThrows();\n");
        sbThrows.append("  }\n");
        sbThrows.append("}\n");
        return sbThrows;
    }
}
