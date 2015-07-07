package pt.ulisboa.tecnico;

/**
 * Anemic class for holding the main java file string.
 */
public class MainClass {
    private final StringBuilder javaFile;
    private final String fileName;
    private final String directoryName;
    private final String fullyQualifiedName;

    public MainClass(StringBuilder javaFile, String fileName,
                     String directoryName, String fullyQualifiedName) {
        this.javaFile = javaFile;
        this.fileName = fileName;
        this.directoryName = directoryName;
        this.fullyQualifiedName = fullyQualifiedName;
    }

    public StringBuilder getJavaFile() {
        return javaFile;
    }

    public String getFileName() {
        return fileName;
    }

    public String getDirectoryName() {
        return directoryName;
    }

    public String getFullyQualifiedName() {
        return fullyQualifiedName;
    }
}
