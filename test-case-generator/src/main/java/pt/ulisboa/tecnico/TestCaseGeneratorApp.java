package pt.ulisboa.tecnico;

import cute.Cute;
import cute.concolic.logging.BranchCoverageLog;
import cute.concolic.logging.JUnitTestGenerator;
import pt.ulisboa.tecnico.internal.InteractiveModeImpl;
import pt.ulisboa.tecnico.internal.NullInteractiveMode;

import javax.tools.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Collection;

/**
 * Main entry for generating test cases.
 */
public class TestCaseGeneratorApp {
    private String mainGenDestFolder = "generated-sources";
    private String mainCompileDestFolder = "classes";
    private String mainInstrDestJar = "jmlcute-processed-classes.jar";
    private String testCasesDestFolder = "generated-test-sources";
    private String covLogDestFolder = "cov-log";
    private InteractiveMode interactiveMode = new NullInteractiveMode();
    private int concolicIterations = 10;
    private boolean resetSearch = true;
    private int concolicIteration = 0;

    public String getMainGenDestFolder() {
        return mainGenDestFolder;
    }

    public String getMainCompileDestFolder() {
        return mainCompileDestFolder;
    }

    public String getMainInstrDestJar() {
        return mainInstrDestJar;
    }

    public String getTestCasesDestFolder() {
        return testCasesDestFolder;
    }

    public String getCovLogDestFolder() {
        return covLogDestFolder;
    }

    public String getClasspath() {
        return System.getProperty("java.class.path");
    }

    public int getConcolicIterations() {
        return concolicIterations;
    }

    public InteractiveMode getInteractiveMode() {
        return interactiveMode;
    }

    public void resetConcolicExecution() {
        resetSearch = true;
        concolicIteration = 0;
    }

    /**
     * Instrument and concolically execute each public instance method of each
     * class under test.
     *
     * @param args the arguments.
     */
    public static void main(String[] args) throws IOException {
        TestCaseGeneratorApp app = new TestCaseGeneratorApp();
        final int index = app.processArguments(args);
        if (index == -1) {
            return;
        }
        final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        final DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<JavaFileObject>();
        final StandardJavaFileManager fileManager = compiler
                .getStandardFileManager(diagnostics, null, null);
        final MainGenerator mainGenerator = new MainGenerator();
        for (int i = index; i < args.length; i++) {
            final String fullyQualifiedName = args[i];
            final MainClass[] mainClasses;
            try {
                mainClasses = mainGenerator.generate(fullyQualifiedName);
            } catch (ClassNotFoundException e) {
                e.printStackTrace();
                break;
            }
            mainClass:
            for (MainClass mainClass : mainClasses) {
                final boolean compiled = app.compileMainClass(compiler,
                        diagnostics, fileManager, mainClass);
                if (!compiled) {
                    break;
                }
                app.instrumentMain(mainClass);
                app.resetConcolicExecution();
                for (int j = 0; j < app.getConcolicIterations(); j++) {
                    final int exit = app.runMain(mainClass);
                    if (exit == -1) {
                        break mainClass;
                    }
                    app.generateJUnitTestCase(mainClass, exit);
                    if (app.isExitState(exit, Cute.EXIT_COMPLETE)) {
                        break;
                    }
                }
                app.printCoverageLog(mainClass);
                app.getInteractiveMode().methodConcolicallyExecuted();
            }
        }
        fileManager.close();
    }

    /*******************
     * Private methods *
     *******************/

    /**
     * Processes arguments.
     *
     * @param args the arguments to process.
     * @return the index of the first not processed argument, or -1, if no arguments are left to process.
     */
    private int processArguments(String[] args) {
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("--help")) {
                System.out.print("Usage:\n" +
                        " -main-generate-d <directory for the generated main java files>\n" +
                        " -main-compile-d <directory for the compiled main java classes>\n" +
                        " -main-instrument-d <directory for the instrumented main classes>\n" +
                        " -test-cases-d <directory for the generated test cases>\n" +
                        " -i <concolic iterations per class>\n" +
                        " <fully qualified name of class> (1 or more class names)\n");
                return -1;
            } else if (args[i].equals("-main-generate-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -main-generate-d.");
                    return -1;
                } else {
                    mainGenDestFolder = args[++i];
                }
            } else if (args[i].equals("-main-compile-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -main-compile-d.");
                    return -1;
                } else {
                    mainCompileDestFolder = args[++i];
                }
            } else if (args[i].equals("-main-instrument-jar")) {
                if (i + 1 >= args.length) {
                    System.err.println("No jar name was specified after " +
                            "-main-instrument-jar.");
                    return -1;
                } else {
                    mainInstrDestJar = args[++i];
                }
            } else if (args[i].equals("-test-cases-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -test-cases-d.");
                    return -1;
                } else {
                    testCasesDestFolder = args[++i];
                }
            } else if (args[i].equals("-cov-log-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -cov-log-d.");
                    return -1;
                } else {
                    covLogDestFolder = args[++i];
                }
            } else if (args[i].equals("-interactive")) {
                interactiveMode = new InteractiveModeImpl();
            } else if (args[i].equals("-i")) {
                if (i + 1 >= args.length) {
                    System.err.println("No iteration value was specified " +
                            "after -i.");
                    return -1;
                } else {
                    concolicIterations = Integer.parseInt(args[++i]);
                }
            } else {
                return i;
            }
        }
        return -1;
    }

    /**
     * Writes mainClass to a .java file, and compiles it to a .class file.
     *
     * @param compiler    the JavaCompiler.
     * @param diagnostics the DiagnosticCollector.
     * @param fileManager the JavaFileManager.
     * @param mainClass   the MainClass to compile.
     * @return true, if mainClass was compiled. Otherwise, false.
     * @throws IOException
     */
    private boolean compileMainClass(
            JavaCompiler compiler,
            DiagnosticCollector<JavaFileObject> diagnostics,
            StandardJavaFileManager fileManager,
            MainClass mainClass) throws IOException {
        final File dir = new File(getMainGenDestFolder(), mainClass
                .getDirectoryName());
        dir.mkdirs();
        final File f = new File(dir, mainClass.getFileName());
        final BufferedWriter writer = new BufferedWriter(new FileWriter(f));
        writer.write(mainClass.getJavaFile().toString());
        writer.close();
        final Collection<String> options = new ArrayList<String>();
        options.add("-classpath");
        options.add(getClasspath());
        options.add("-d");
        options.add(getMainCompileDestFolder());
        final Iterable<? extends JavaFileObject> compilationUnits = fileManager
                .getJavaFileObjects(f);
        final boolean compiled = compiler.getTask(null, fileManager,
                diagnostics, options, null, compilationUnits).call();
        if (compiled) {
            return true;
        } else {
            System.err.println("The generated class has errors. Something " +
                    "terribly wrong has happened.");
            for (Diagnostic diagnostic : diagnostics.getDiagnostics()) {
                System.err.println(diagnostic);
            }
            return false;
        }
    }

    /**
     * Instruments mainClass in a different process using CuteInstrumenter.
     *
     * @param mainClass the MainClass to instrument.
     */
    private void instrumentMain(MainClass mainClass) throws IOException {
        final ProcessBuilder pb = new ProcessBuilder("java",
                "-cp", getClasspath(),
                "-Dcute.sequential=" + System.getProperty("cute.sequential"),
                "cute.instrument.CuteInstrumenter",
                "-keep-line-number",
                "-d", getMainInstrDestJar(),
                "-outjar",
                "-x", "cute", "-x", "lpsolve",
                "--app", mainClass.getFullyQualifiedName());
        final Process process = pb.start();
        final Thread input, error;
        (input = new Thread(new Runnable() {
            public void run() {
                final BufferedReader br = new BufferedReader(
                        new InputStreamReader(process.getInputStream()));
                try {
                    String line, secondToLastLine = "";
                    while ((line = br.readLine()) != null) {
                        secondToLastLine = line;
                    }
                    System.out.println(secondToLastLine);
                    br.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        })).start();
        (error = new Thread(new Runnable() {
            public void run() {
                final BufferedReader br = new BufferedReader(
                        new InputStreamReader(process.getErrorStream()));
                String line;
                try {
                    while ((line = br.readLine()) != null) {
                        System.err.println(line);
                    }
                    br.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        })).start();
        try {
            input.join();
            error.join();
            process.waitFor();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Calls the instrumented mainClass in a different process.
     *
     * @param mainClass the MainClass to run.
     * @return -1, if there was an error. Otherwise, the exit code of the
     * process.
     */
    private int runMain(MainClass mainClass) throws IOException {
        int exit;
        final ProcessBuilder pb = new ProcessBuilder("java",
                "-classpath", getMainInstrDestJar() + ":" + getClasspath(),
                "-Djava.library.path=" + System.getProperty("java.library.path"),
                "-Dcute.args=" + System.getProperty("cute.args") + (resetSearch
                        ? ":-m:2" : ""),
                mainClass.getFullyQualifiedName());
        final Process process = pb.start();
        final Thread input, error;
        (input = new Thread(new Runnable() {
            public void run() {
                final BufferedReader brInput = new BufferedReader(
                        new InputStreamReader(process.getInputStream()));
                String line;
                try {
                    while ((line = brInput.readLine()) != null) {
                        System.out.println(line);
                    }
                    brInput.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        })).start();
        (error = new Thread(new Runnable() {
            public void run() {
                final BufferedReader brError = new BufferedReader(
                        new InputStreamReader(process.getErrorStream()));
                String line;
                try {
                    while ((line = brError.readLine()) != null) {
                        System.err.println(line);
                    }
                    brError.close();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        })).start();
        try {
            input.join();
            error.join();
            exit = process.waitFor();
        } catch (InterruptedException e) {
            e.printStackTrace();
            exit = -1;
        }
        if (exit != -1) {
            resetSearch = false;
        }
        return exit;
    }

    /**
     * Checks whether exit has the Cute state state.
     *
     * @param exit  the exit code to check.
     * @param state the state to check.
     * @return true, if the exit code has the state state. Otherwise, false.
     */
    private boolean isExitState(int exit, int state) {
        return (exit & state) == state;
    }

    /**
     * Generates the test case resulting from the last concolic execution.
     * TODO: Only generate, if the test case increases coverage and does not violate an assumption: isExitState(exit, Cute.EXIT_ASSUME_FAILED) || !isExitState(exit, Cute.EXIT_COVERAGE_INCREASED).
     *
     * @param mainClass the MainClass to generate test cases for.
     * @param exit      the exit code of the previous concolic execution.
     * @return true, if the test case was generated. Otherwise, false.
     */
    private boolean generateJUnitTestCase(MainClass mainClass, int exit) {
        final String fullName = mainClass.getFullyQualifiedName();
        final String pack = fullName.substring(0, fullName.lastIndexOf('.'));
        final String name = fullName.substring(fullName.lastIndexOf('.') + 1);
        final StringBuilder comment = new StringBuilder();
        if (isExitState(exit, Cute.EXIT_ASSUME_FAILED)) {
            comment.append("This test case causes an assumption violation.\n");
        }
        if (isExitState(exit, Cute.EXIT_COVERAGE_INCREASED)) {
            comment.append("This test case increases coverage.\n");
        }
        if (isExitState(exit, Cute.EXIT_ASSERT_FAILED)) {
            comment.append("This test case causes a specification violation.\n");
        }
        JUnitTestGenerator.setForceCreation(concolicIteration == 0);
        final boolean appended = JUnitTestGenerator.appendToJunitTestCase(
                getTestCasesDestFolder(), pack, name, concolicIteration,
                comment.toString());
        if (appended) {
            concolicIteration++;
        }
        return appended;
    }

    /**
     * Prints the coverage log of the previous concolic execution.
     *
     * @param mainClass the class executed in the previous concolic execution.
     * @throws FileNotFoundException if the log could not be found.
     */
    private void printCoverageLog(MainClass mainClass) throws FileNotFoundException {
        final File covDir = new File(getCovLogDestFolder());
        covDir.mkdirs();
        final File covLogFile = new File(covDir, mainClass.getFileName());
        final PrintStream ps = new PrintStream(new BufferedOutputStream(
                new FileOutputStream(covLogFile)));
        BranchCoverageLog.printCoverageLog(ps);
        ps.close();
    }
}
