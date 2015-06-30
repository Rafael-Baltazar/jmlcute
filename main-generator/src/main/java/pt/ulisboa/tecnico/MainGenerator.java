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
     * @param fullyQualifiedClassName the fully qualified class name of the class under test.
     * @return the array with the StringBuffer's each with a java file for a method.
     */
    public StringBuilder[] generate(String fullyQualifiedClassName) throws ClassNotFoundException {
        Collection<StringBuilder> result = new ArrayList<StringBuilder>();
        Class clazz = Class.forName(fullyQualifiedClassName);
        Method[] methods = clazz.getDeclaredMethods();
        for (Method method : methods) {
            final int modifiers = method.getModifiers();
            if (Modifier.isPublic(modifiers) && !Modifier.isStatic(modifiers)) {
                Type[] parameterTypes = method.getGenericParameterTypes();
                StringBuilder sb = generateMethod(fullyQualifiedClassName,
                        method.getName(), parameterTypes);
                result.add(sb);
            }
        }
        return result.toArray(new StringBuilder[0]);
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
     * Appends a java class header to sb. Example: com.App.main(App a, Integer
     * i) will become "public class jmlcute__com__App__main_App_Integer {\n"
     *
     * @param fullyQualifiedClassName the fully qualified name of the class
     *                                under test.
     * @param functionName            the name of the function under test.
     * @param parameterTypes          the types of the parameters of the
     *                                function under test.
     * @param sb                      the StringBuilder to append to.
     * @return sb with the appended Java class header.
     */
    private StringBuilder appendJavaClassHeader(
            String fullyQualifiedClassName, String functionName,
            Type[] parameterTypes, StringBuilder sb) {
        sb.append(indentation).append("public class jmlcute__")
                .append(fullyQualifiedClassName.replaceAll("\\.", "__"))
                .append("__").append(functionName).append("_");
        String separator = "";
        for (Type type : parameterTypes) {
            String typeName = ((Class) type).getName().replaceAll("\\.", "__");
            sb.append(separator).append(typeName);
            separator = "_";
        }
        return sb.append(" {\n");
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
                .append(" receiver = cute.Cute.input.Object(\"")
                .append(fullyQualifiedClasName).append("\");\n");
        sb.append(indentation).append("cute.Cute.Assume(receiver != null);\n");
        for (int i = 0; i < parameterTypes.length; i++) {
            String typeName = ((Class) parameterTypes[i]).getName();
            sb.append(indentation).append(typeName).append(" arg").append(i)
                    .append(" = cute.Cute.input.Object(\"").append(typeName)
                    .append("\");\n");
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
