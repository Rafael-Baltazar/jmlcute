package pt.ulisboa.tecnico;

import cute.Cute;
import cute.concolic.Globals;
import cute.concolic.logging.BranchCoverageLog;

import javax.tools.*;
import java.io.*;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Collection;

/**
 * Main entry for MainGenerator.
 */
public class TestCaseGeneratorApp {
    private String mainGenDestFolder = "generated-sources";
    private String mainCompileDestFolder = "classes";
    private String mainInstrDestFolder = "classes";
    private String mainInstrDestJar = "jmlcute-processed-classes.jar";
    private String testCasesDestFolder = "generated-test-sources";
    private int concolicIterations = 3;

    public String getMainGenDestFolder() {
        return mainGenDestFolder;
    }

    public String getMainCompileDestFolder() {
        return mainCompileDestFolder;
    }

    public String getMainInstrDestFolder() {
        return mainInstrDestFolder;
    }

    public String getMainInstrDestJar() {
        return mainInstrDestJar;
    }

    public String getTestCasesDestFolder() {
        return testCasesDestFolder;
    }

    public int getConcolicIterations() {
        return concolicIterations;
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
                boolean compiled = app.compileMainClass(compiler, diagnostics,
                        fileManager, mainClass);
                if (!compiled) {
                    break;
                }
                app.instrumentMain(mainClass);
                for (int j = 0; j < app.getConcolicIterations(); j++) {
                    Globals.globals = new Globals();
                    try {
                        boolean run = app.runMain(mainClass);
                        if (!run) {
                            continue mainClass;
                        }
                    } catch (InvocationTargetException e) {
                        System.err.println(e.getCause().toString());
                    }
                    if (Globals.globals.information.isReturnVal(Cute.
                            EXIT_COMPLETE)) {
                        break;
                    }
                }
                BranchCoverageLog.main(new String[]{"."});
            }
        }
        fileManager.close();
    }

    /*******************
     * Private methods *
     *******************/

    /**
     * Processes arguments
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
            } else if (args[i].equals("-main-instrument-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -main-instrument-d.");
                    return -1;
                } else {
                    mainInstrDestFolder = args[++i];
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
     * @param compiler    the JavaCompiler.
     * @param diagnostics the DiagnosticCollector.
     * @param fileManager the JavaFileManager.
     * @param mainClass   the MainClass to compile.
     * @return true, if mainClass was compiled. Otherwise, false.
     * @throws IOException
     */
    private boolean compileMainClass(JavaCompiler compiler,
                                     DiagnosticCollector<JavaFileObject>
                                             diagnostics,
                                     StandardJavaFileManager fileManager,
                                     MainClass mainClass) throws IOException {
        final File f = new File(getMainGenDestFolder() + "/" + mainClass
                .getDirectoryName(), mainClass.getFileName());
        if (f.exists()) {
            f.delete();
        } else {
            f.getParentFile().mkdirs();
            f.createNewFile();
        }
        final BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(f), "UTF-8"));
        writer.write(mainClass.getJavaFile().toString());
        writer.close();
        final Collection<String> options = new ArrayList<String>();
        options.add("-classpath");
        options.add(System.getProperty("java.class.path"));
        options.add("-d");
        options.add(getMainCompileDestFolder());
        final Iterable<? extends JavaFileObject> compilationUnits = fileManager
                .getJavaFileObjects(f);
        final boolean compiled = compiler.getTask(null, fileManager, diagnostics,
                options, null, compilationUnits).call();
        if (compiled) {
            return true;
        } else {
            System.err.println("The generated classes have errors. Something " +
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
                "-cp", System.getProperty("java.class.path"),
                "-Dcute.sequential=true",
                "cute.instrument.CuteInstrumenter",
                "-keep-line-number",
                "-d", getMainInstrDestFolder() + "/" + getMainInstrDestJar(),
                "-outjar",
                "-x", "cute", "-x", "lpsolve",
                "--app", mainClass.getFullyQualifiedName());
        final Process process = pb.start();
        BufferedReader br = new BufferedReader(new InputStreamReader(
                process.getInputStream()));
        String line;
        while ((line = br.readLine()) != null) {
            System.err.println(line);
        }
    }

    /**
     * @param mainClass the MainClass to run.
     * @return true, if mainClass was run. Otherwise, false.
     */
    private boolean runMain(MainClass mainClass) throws InvocationTargetException {
        final File f = new File(getMainInstrDestFolder(), getMainInstrDestJar());
        try {
            final URLClassLoader classLoader = new URLClassLoader(new URL[]{
                    f.toURI().toURL()}, this.getClass().getClassLoader());
            final Class clazz = Class.forName(mainClass.getFullyQualifiedName(),
                    true, classLoader);
            final Method m = clazz.getDeclaredMethod("main", String[].class);
            final String[] params = null;
            m.invoke(null, (Object) params);
            return true;
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        } catch (MalformedURLException e) {
            e.printStackTrace();
        } catch (IllegalAccessException e) {
            e.printStackTrace();
        }
        return false;
    }
}
