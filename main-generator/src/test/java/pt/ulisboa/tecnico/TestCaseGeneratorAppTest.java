package pt.ulisboa.tecnico;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import java.io.IOException;

/**
 * Unit test for simple TestCaseGeneratorApp.
 */
public class TestCaseGeneratorAppTest extends TestCase {
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public TestCaseGeneratorAppTest(String testName) {
        super(testName);
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite() {
        return new TestSuite(TestCaseGeneratorAppTest.class);
    }

    /**
     * Generate JUnit test cases for three classes in samplePackageName.
     */
    public void testSamplePackageNamePackage() {
        final String[] args = new String[]{
                "samplePackageName.DeadlockExample",
                "samplePackageName.SampleSuperclassName",
                "samplePackageName.SampleClassName"};
        try {
            TestCaseGeneratorApp.main(args);
        } catch (IOException e) {
            fail();
        }
    }
}
