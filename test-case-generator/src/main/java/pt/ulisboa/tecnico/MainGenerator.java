package pt.ulisboa.tecnico;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;

/**
 * Generates java files for each of the methods of the class under test. Each
 * of the java files will
 */
public class MainGenerator {
    private Indentation indentation;
    private final Map<String, String> inputTypes;

    public MainGenerator() {
        inputTypes = new TreeMap<String, String>();
        inputTypes.put("boolean", "Boolean()");
        inputTypes.put("short", "Short()");
        inputTypes.put("int", "Integer()");
        inputTypes.put("long", "Long()");
        inputTypes.put("float", "Float()");
        inputTypes.put("double", "Double()");
        inputTypes.put("char", "Character()");
        inputTypes.put("byte", "Byte()");
    }

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
        for (final Method method : methods) {
            final int modifiers = method.getModifiers();
            if (Modifier.isPublic(modifiers) && !Modifier.isStatic(modifiers)) {
                final Type[] parameterTypes = method.getGenericParameterTypes(),
                        exceptionTypes = method.getGenericExceptionTypes();
                final String methodName = method.getName(),
                        fileName = appendJavaClassName(fullyQualifiedName,
                                methodName, parameterTypes, new StringBuilder())
                                .append(".java").toString(),
                        pack = fullyQualifiedName.substring(0,
                                fullyQualifiedName.lastIndexOf('.')),
                        directoryName = pack.replaceAll("\\.", "/");
                final StringBuilder javaFile = generateMethod(
                        fullyQualifiedName, methodName, parameterTypes,
                        exceptionTypes),
                        fullJavaClassName = new StringBuilder();
                fullJavaClassName.append(pack).append(".");
                appendJavaClassName(fullyQualifiedName, methodName,
                        parameterTypes, fullJavaClassName);
                final MainClass mainClass = new MainClass(javaFile, fileName,
                        directoryName, fullJavaClassName.toString());
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
                                         Type[] parameterTypes,
                                         Type[] exceptionTypes) {
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
        final String pack = fullyQualifiedClassName.substring(0, fullyQualifiedClassName.lastIndexOf('.'));
        return sb.append(indentation).append("package ").append(pack).append(";\n");
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
                .replaceAll("\\.", "__")).append("__").append(methodName);
        for (Type type : parameterTypes) {
            String typeName = ((Class) type).getName().replaceAll("\\.", "__");
            sb.append("_").append(typeName);
        }
        return sb;
    }

    private StringBuilder appendJavaClassFooter(StringBuilder sb) {
        return sb.append(indentation).append("}\n");
    }

    private StringBuilder appendMainHeader(StringBuilder sb) {
        return sb.append(indentation)
                .append("public static void main(String[] args) throws Throwable {\n");
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
            final String typeName = ((Class) parameterTypes[i]).getName();
            String inputType = inputTypes.get(typeName);
            sb.append(indentation).append(typeName).append(" arg").append(i)
                    .append(" = (").append(typeName).append(") cute.Cute.input.");
            if (inputType == null) {
                sb.append("Object(\"").append(typeName).append("\")");
            } else {
                sb.append(inputType);
            }
            sb.append(";\n");
        }
        sb.append(indentation).append("receiver.").append(functionName).append("(");
        String separator = "";
        for (int i = 0; i < parameterTypes.length; i++) {
            sb.append(separator).append("arg").append(i);
            separator = ", ";
        }
        sb.append(");\n");
        return sb;
    }
}
