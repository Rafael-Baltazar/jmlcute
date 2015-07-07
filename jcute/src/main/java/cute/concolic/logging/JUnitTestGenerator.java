package cute.concolic.logging;

import com.thoughtworks.qdox.JavaDocBuilder;
import com.thoughtworks.qdox.model.JavaClass;
import com.thoughtworks.qdox.model.JavaMethod;
import com.thoughtworks.qdox.model.JavaParameter;
import com.thoughtworks.qdox.model.JavaSource;
import cute.concolic.Information;

import java.io.*;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

/**
 * Created by IntelliJ IDEA.
 * User: Koushik Sen (ksen@cs.uiuc.edu)
 * Date: Dec 16, 2005
 * Time: 1:28:35 PM
 */
public class JUnitTestGenerator {
    private Information information;
    private static boolean forceCreation = true;
    private HashMap omap = new HashMap();
    private Vector stmts = new Vector();
    private String type;
    private String var;
    private int i = 0;
    private int sz = 0;
    public static final String junitInputFile = "cuteJUnitInput";

    public JUnitTestGenerator(Information information) {
        this.information = information;
    }

    /**
     * Sets the forceCreation attribute to value. forceCreation will overwrite
     * the old test case file, when appending to it. Default value is true.
     *
     * @param value the value to set.
     */
    public static void setForceCreation(boolean value) {
        JUnitTestGenerator.forceCreation = value;
    }

    public void assignToInput(String type) {
        if (information.generateJUnit) {
            this.type = type;
            this.var = "input[i++]";
            sz++;
        }
    }

    public void assignTo(String varName, String field, String type) {
        if (information.generateJUnit) {
            this.type = type;
            this.var = varName + "." + field;
        }
    }

    public String valueObjectNull() {
        if (information.generateJUnit) {
            stmts.add(var + " = null;");
        }
        return null;
    }

    public String valueObject(int oid, String type) {
        return valueObject(oid, type, null);
    }

    public String valueObject(int oid, String type, Object ret) {
        if (information.generateJUnit) {
            Integer tmp = new Integer(oid);
            String tmpstr = "tmp" + (++i);
            if (omap.containsKey(tmp)) {
                stmts.add(type + " " + tmpstr + " = " + omap.get(tmp) + ";");
            } else {
                if (ret == null)
                    stmts.add(type + " " + tmpstr + " = new " + type + "();");
                else if (ret.equals("java.lang.Integer") ||
                        ret.equals("java.lang.Long") ||
                        ret.equals("java.lang.Short") ||
                        ret.equals("java.lang.Byte") ||
                        ret.equals("java.lang.Boolean") ||
                        ret.equals("java.lang.Character") ||
                        ret.equals("java.lang.Double") ||
                        ret.equals("java.lang.Float"))
                    stmts.add(type + " " + tmpstr + " = new " + type + "(" + ret + ");");
                else
                    stmts.add(type + " " + tmpstr + " = new " + type + "(\"" + ret + "\");");
                omap.put(tmp, tmpstr);
            }
            stmts.add(var + " = " + tmpstr + ";");
            return tmpstr;
        } else
            return null;
    }

    public void valuePrimitive(Object ret) {
        if (information.generateJUnit) {
            if (var.indexOf('.') > 0) {
                stmts.add(var + " = " + ret + ";");
            } else {
                stmts.add(var + " = new " + type + "(" + ret + ");");
            }
        }
    }

    public void printAll() {
        if (information.generateJUnit) {
            try {
                PrintWriter out = new PrintWriter(new BufferedWriter(
                        new FileWriter(junitInputFile)));
                out.println("input = new Object[" + sz + "];");
                for (Iterator iterator = stmts.iterator(); iterator.hasNext(); ) {
                    String s = (String) iterator.next();
                    out.println(s);
                }
                out.close();
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }
    }

    public static void deleteJunitTestCase(String dir, String cName) {
        File f = getJUnitFileName(dir, cName);
        if (f != null && f.exists()) {
            f.delete();
        }
    }

    public static File getJUnitFileName(String dir, String cName) {
        if (cName != null) {
            StringBuilder sb = new StringBuilder();
            appendJUnitClassName(sb, cName).append(".java");
            String fileName = sb.toString();
            return new File(dir.trim().equals("") ? null : dir, fileName);
        }
        return null;
    }

    private static boolean isTestPresent(File f, String methodName) {
        JavaSource source;
        boolean flag = false;
        JavaDocBuilder builder = new JavaDocBuilder();
        try {
            builder.addSource(f);
            source = builder.getSources()[0];
            JavaClass[] javaClasses = source.getClasses();
            for (int i = 0; !flag && i < javaClasses.length; i++) {
                JavaClass javaClass = javaClasses[i];
                JavaMethod[] methods = javaClass.getMethods();
                for (int j = 0; !flag && j < methods.length; j++) {
                    JavaMethod method = methods[j];
                    if (method.getName().equals(methodName)) {
                        JavaParameter[] parameters = method.getParameters();
                        if (parameters.length == 0) {
                            flag = true;
                        }
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return flag;
    }

    /**
     * Appends a junit test case number i to a file. Assumes the junit input
     * file is in ".".
     *
     * @param dir   the output directory for the JUnit file.
     * @param pkg   the package name of the class under test.
     * @param cName the name of the class under test.
     * @param i     the ith test.
     * @return true, if the test case was appended. Otherwise, false.
     */
    public static boolean appendToJunitTestCase(
            String dir, String pkg, String cName, int i, String comment) {
        return appendToJunitTestCase(dir, pkg, cName, i, new File("."), comment);
    }

    /**
     * Appends a junit test case number testId to a file.
     *
     * @param dir     the output directory for the JUnit file.
     * @param pkg     the package name of the class under test.
     * @param cName   the name of the class under test.
     * @param testId  typically the testId-th test.
     * @param lastDir the dir with junitInputFile file.
     * @param comment an explanatory comment of the test case.
     * @return true, if the test case was appended. Otherwise, false.
     */
    public static boolean appendToJunitTestCase(String dir, String pkg,
                                                String cName, int testId,
                                                File lastDir, String comment) {
        File f = getJUnitFileName(dir, cName);
        try {
            if (!f.exists()) {
                createFile(f, pkg, cName);
            } else if (forceCreation) {
                f.delete();
                createFile(f, pkg, cName);
            }
            if (isTestPresent(f, "test" + testId)) {
                return false;
            }
            RandomAccessFile rf = new RandomAccessFile(f, "rws");
            byte[] buf = new byte[1024];
            int count = 0;
            int lastPos = -1;
            int len;
            while ((len = rf.read(buf)) != -1) {
                for (int j = 0; j < len; j++) {
                    if (buf[j] == '}') {
                        lastPos = count;
                    }
                    count++;
                }
            }
            if (lastPos >= 0) {
                rf.setLength(lastPos);
                rf.seek(lastPos);
            }
            appendFile(rf, testId, cName, lastDir, comment);
            rf.writeBytes("}\n");
            rf.close();
            return true;
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        }
    }

    /**
     * Appends junit input file to rf.
     *
     * @param rf      the RandomAccessFile to write to.
     * @param i       the id of the test case.
     * @param cName   the name of the class under test.
     * @param lastDir the dir with the junit input file.
     * @param comment an explanatory comment of the test case.
     */
    private static void appendFile(RandomAccessFile rf, int i, String cName, File lastDir, String comment) {
        try {
            String str;
            BufferedReader in = new BufferedReader(new FileReader(
                    new File(lastDir, junitInputFile)));
            if (!comment.isEmpty()) {
                rf.writeBytes("    /**\n");
                String[] split = comment.split("\n");
                for (String s : split) {
                    rf.writeBytes("     * " + s + "\n");
                }
                rf.writeBytes("     */\n");
            }
            rf.writeBytes("    public void test" + i + "(){\n");
            rf.writeBytes("        i=0;\n");
            while ((str = in.readLine()) != null) {
                rf.writeBytes("        ");
                rf.writeBytes(str);
                rf.writeByte('\n');
            }
            in.close();
            rf.writeBytes("        i=0;\n");
            rf.writeBytes("        cute.Cute.input = this;\n");
            rf.writeBytes("        " + cName + ".main(null);\n    }\n\n");
        } catch (IOException e) {
            e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.
        }
    }

    private static StringBuilder appendJUnitClassName(StringBuilder s, String cName) {
        return s.append("jmlcute__").append(cName.replaceAll("\\.", "_")).append("_Test");
    }

    private static String getJUnitClassName(String cName) {
        return appendJUnitClassName(new StringBuilder(), cName).toString();
    }

    /**
     * Writes the modified template to f.
     *
     * @param f     the file to create.
     * @param pkg   the package of the class under test.
     * @param cName the name of the class under test.
     */
    private static void createFile(File f, String pkg, String cName) throws IOException {
        String str;
        String rep = getJUnitClassName(cName);
        BufferedReader in = new BufferedReader(new InputStreamReader(JUnitTestGenerator
                .class.getClassLoader()
                .getResourceAsStream("cute/concolic/logging/Template.java")));
        PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(f)));
        if (pkg != null && !pkg.trim().equals("")) {
            out.println("package " + pkg + ";");
        }
        while ((str = in.readLine()) != null) {
            str = str.replaceAll("\\$Template\\$", rep);
            out.println(str);
        }
        in.close();
        out.close();
    }
}
