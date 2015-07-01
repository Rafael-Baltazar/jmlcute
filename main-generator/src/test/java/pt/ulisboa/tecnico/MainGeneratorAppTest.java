package pt.ulisboa.tecnico;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import java.io.IOException;

/**
 * Unit test for simple MainGeneratorApp.
 */
public class MainGeneratorAppTest extends TestCase {
    /**
     * Create the test case
     *
     * @param testName name of the test case
     */
    public MainGeneratorAppTest(String testName) {
        super(testName);
    }

    /**
     * @return the suite of tests being tested
     */
    public static Test suite() {
        return new TestSuite(MainGeneratorAppTest.class);
    }

    /**
     * Rigourous Test :-)
     */
    public void testApp() {
        final String[] args = new String[]{
                "-d", "test-classes",
                "samplePackageName.SampleSuperclassName"};
        try {
            MainGeneratorApp.main(args);
        } catch (IOException e) {
            fail();
        }
    }
}
