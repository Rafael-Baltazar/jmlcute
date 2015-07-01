package pt.ulisboa.tecnico;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;

/**
 * Generates java files for each of the methods of the class under test. Each of the java files will
 */
public class MainGenerator {
    private Indentation indentation;

    /**
     * Generates a java file for each of the public instance (non-static)
     * methods declared in fullyQualifiedClassName.
     *
     * @param fullyQualifiedName the fully qualified class name of the class under test.
     * @return the array with the StringBuffer's each with a java file for a method.
     */
    public MainClass[] generate(String fullyQualifiedName) throws ClassNotFoundException {
        final Collection<MainClass> result = new ArrayList<MainClass>();
        final Class clazz = Class.forName(fullyQualifiedName);
        final Method[] methods = clazz.getDeclaredMethods();
        for (Method method : methods) {
            final int modifiers = method.getModifiers();
            if (Modifier.isPublic(modifiers) && !Modifier.isStatic(modifiers)) {
                final Type[] parameterTypes = method.getGenericParameterTypes();
                final String methodName = method.getName(),
                        fileName = appendJavaClassName(fullyQualifiedName,
                                methodName, parameterTypes, new StringBuilder())
                                .append(".java").toString();
                final StringBuilder sb = generateMethod(fullyQualifiedName,
                        methodName, parameterTypes),
                        directoryName = new StringBuilder(),
                        fullJavaClassName = new StringBuilder();
                final String[] split = fullyQualifiedName.split("\\.");
                String sepSlash = "";
                for (int i = 0; i < split.length - 1; i++) {
                    directoryName.append(sepSlash).append(split[i]);
                    fullJavaClassName.append(split[i]).append(".");
                    sepSlash = "/";
                }
                appendJavaClassName(fullyQualifiedName, methodName,
                        parameterTypes, fullJavaClassName);
                final MainClass mainClass = new MainClass(sb, fileName,
                        directoryName.toString(), fullJavaClassName.toString());
                result.add(mainClass);
            }
        }
        return result.toArray(new MainClass[0]);
    }

    /*******************
     * Private methods *
     *******************/

    /**
     * Generates a Java file with a main for the given method signature elements.
     *
     * @param fullyQualifiedClassName the fully qualified of the class under test.
     * @param functionName            the name of the method under test.
     * @param parameterTypes          the parameter types of the method under test.
     * @return the StringBuilder with the generated java file for the method.
     */
    private StringBuilder generateMethod(String fullyQualifiedClassName,
                                         String functionName,
                                         Type[] parameterTypes) {
        final StringBuilder sb = new StringBuilder();
        indentation = new Indentation();
        appendPackage(fullyQualifiedClassName, sb);
        sb.append("\n");
        appendJavaClassHeader(fullyQualifiedClassName, functionName,
                parameterTypes, sb);
        indentation.increase();
        appendMainHeader(sb);
        indentation.increase();
        appendMainBody(fullyQualifiedClassName, functionName, parameterTypes,
                sb);
        indentation.decrease();
        appendMainFooter(sb);
        indentation.decrease();
        appendJavaClassFooter(sb);
        return sb;
    }

    /**
     * Appends the package name to sb given the fullyQualifiedClassName.
     *
     * @param fullyQualifiedClassName the fully qualified of the class under
     *                                test.
     * @param sb                      the StringBuilder to append to.
     * @return sb with the appended package.
     */
    private StringBuilder appendPackage(String fullyQualifiedClassName,
                                        StringBuilder sb) {
        sb.append(indentation).append("package ");
        String[] split = fullyQualifiedClassName.split("\\.");
        String separator = "";
        for (int i = 0; i < split.length - 1; i++) {
            sb.append(separator).append(split[i]);
            separator = ".";
        }
        return sb.append(";\n");
    }

    /**
     * Appends a java class header to sb. Example: com.samplePackageName.main(samplePackageName a, Integer
     * i) will become "public class jmlcute__com__App__main_App_Integer {\n"
     *
     * @param fullyQualifiedName the fully qualified name of the class
     *                           under test.
     * @param methodName         the name of the function under test.
     * @param parameterTypes     the types of the parameters of the
     *                           function under test.
     * @param sb                 the StringBuilder to append to.
     * @return sb with the appended Java class header.
     */
    private StringBuilder appendJavaClassHeader(String fullyQualifiedName,
                                                String methodName,
                                                Type[] parameterTypes,
                                                StringBuilder sb) {
        sb.append(indentation).append("public class ");
        appendJavaClassName(fullyQualifiedName, methodName, parameterTypes, sb);
        return sb.append(" {\n");
    }

    private StringBuilder appendJavaClassName(String fullyQualifiedClassName,
                                              String methodName,
                                              Type[] parameterTypes,
                                              StringBuilder sb) {
        sb.append("jmlcute__").append(fullyQualifiedClassName
                .replaceAll("\\.", "__")).append("__").append(methodName)
                .append("_");
        String separator = "";
        for (Type type : parameterTypes) {
            String typeName = ((Class) type).getName().replaceAll("\\.", "__");
            sb.append(separator).append(typeName);
            separator = "_";
        }
        return sb;
    }

    private StringBuilder appendJavaClassFooter(StringBuilder sb) {
        return sb.append(indentation).append("}\n");
    }

    private StringBuilder appendMainHeader(StringBuilder sb) {
        return sb.append(indentation).append("public static void main(String[] args) {\n");
    }

    private StringBuilder appendMainFooter(StringBuilder sb) {
        return sb.append(indentation).append("}\n");
    }

    private StringBuilder appendMainBody(String fullyQualifiedClasName, String functionName, Type[] parameterTypes, StringBuilder sb) {
        sb.append(indentation).append(fullyQualifiedClasName)
                .append(" receiver = (").append(fullyQualifiedClasName)
                .append(") cute.Cute.input.Object(\"").append(fullyQualifiedClasName)
                .append("\");\n");
        sb.append(indentation).append("cute.Cute.Assume(receiver != null);\n");
        for (int i = 0; i < parameterTypes.length; i++) {
            String typeName = ((Class) parameterTypes[i]).getName();
            sb.append(indentation).append(typeName).append(" arg").append(i)
                    .append(" = (").append(typeName).append(") cute.Cute.input.Object(\"")
                    .append(typeName).append("\");\n");
        }
        sb.append(indentation).append("receiver.").append(functionName).append("(");
        String separator = "";
        for (int i = 0; i < parameterTypes.length; i++) {
            sb.append(separator).append("arg").append(i);
            separator = ", ";
        }
        return sb.append(");\n");
    }
}
