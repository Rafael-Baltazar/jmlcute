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
     * System test: java.io.IOException: Operation not permitted at java.io.UnixFileSystem.createFileExclusively(Native Method).
     * After jml compilation.
     */
    public void testNewFileNotPermitted() {
        String[] input = new String[]{
                "-main-generate-d","generated-sources/",
                "-main-compile-d","classes/",
                "-main-instrument-jar","jmlcute-processed-classes.jar",
                "-test-cases-d","generated-test-sources/",
                "SocialEventPlanner_multi_threaded.events.add_disjointness"
        };
        try {
            TestCaseGeneratorApp.main(input);
        } catch (IOException e) {
            fail(e.getMessage());
        }
    }
}
