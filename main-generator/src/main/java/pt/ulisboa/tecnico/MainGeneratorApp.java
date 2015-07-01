package pt.ulisboa.tecnico;

import cute.AssertFailedError;
import cute.Cute;
import cute.concolic.Globals;
import cute.concolic.logging.BranchCoverageLog;
import cute.instrument.CuteInstrumenter;

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
public class MainGeneratorApp {
    private static String destinationFolder = ".";
    private static int concolicIterations = 10;

    /**
     * Instrument and concolically execute each public instance method of each
     * class under test.
     *
     * @param args the arguments.
     */
    public static void main(String[] args) throws IOException {
        final int index = processArguments(args);
        if (index == -1) {
            return;
        }
        final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<JavaFileObject>();
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
                continue;
            }
            mainClass:
            for (MainClass mainClass : mainClasses) {
                try {
                    compileMainClass(compiler, diagnostics, fileManager,
                            mainClass);
                } catch (IOException e) {
                    e.printStackTrace();
                    continue;
                }
                for (Diagnostic diagnostic : diagnostics.getDiagnostics()) {
                    System.err.println(diagnostic);
                }
                if (!diagnostics.getDiagnostics().isEmpty()) {
                    continue;
                }
                final String[] jcuteArgs = new String[]{
                        "-keep-line-number",
                        "-d", destinationFolder,
                        "-x", "cute", "-x", "lpsolve",
                        "--app", mainClass.getFullyQualifiedName()};
                CuteInstrumenter.main(jcuteArgs);
                for (int j = 0; j < concolicIterations; j++) {
                    Globals.globals = new Globals();
                    try {
                        boolean run = runMain(mainClass);
                        if (!run) {
                            continue mainClass;
                        }
                    } catch (InvocationTargetException e) {
                        Throwable t = e.getTargetException();
                        if (t instanceof AssertFailedError) {
                            t.printStackTrace();
                        }
                    }
                    if (Globals.globals.information.isReturnVal(
                            Cute.EXIT_COMPLETE)) {
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
    private static int processArguments(String[] args) {
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("--help")) {
                System.out.print("Usage:\n" +
                        " -d <destination directory>\n" +
                        " -i <concolic iterations per class>\n" +
                        " <fully qualified name of class> (1 or more class names)\n");
                return -1;
            } else if (args[i].equals("-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -d.");
                    return -1;
                } else {
                    destinationFolder = args[++i];
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
     * @throws IOException
     */
    private static void compileMainClass(JavaCompiler compiler,
                                         DiagnosticCollector<JavaFileObject>
                                                 diagnostics,
                                         StandardJavaFileManager fileManager,
                                         MainClass mainClass) throws IOException {
        final Collection<String> options = new ArrayList<String>();
        options.add("-classpath");
        options.add(System.getProperty("java.class.path"));
        final File f = new File(destinationFolder + "/" + mainClass
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
        final Iterable<? extends JavaFileObject> compilationUnits = fileManager
                .getJavaFileObjects(f);
        compiler.getTask(null, fileManager, diagnostics, options, null,
                compilationUnits).call();
    }

    /**
     * @param mainClass the MainClass to run.
     * @return true, if mainClass was run. Otherwise, false.
     */
    private static boolean runMain(MainClass mainClass) throws InvocationTargetException {
        final File f = new File(destinationFolder + "/" + mainClass.
                getDirectoryName(), mainClass.getFileName());
        try {
            final ClassLoader classLoader = URLClassLoader.newInstance(new URL[]{
                    f.toURI().toURL()});
            final Class clazz = classLoader.loadClass(mainClass.
                    getFullyQualifiedName());
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
