package pt.ulisboa.tecnico;

/**
 * Main entry for MainGenerator.
 */
public class MainGeneratorApp {
    private static String destinationFolder = ".";

    /**
     * Processes arguments
     *
     * @param args the arguments to process.
     * @return the index of the first not processed argument, or -1, if no arguments are left to process.
     */
    private static int processArguments(String[] args) {
        for (int i = 0; i < args.length; i++) {
            if (args[i].equals("--help")) {
                System.out.println("Usage: -d <destination directory> <fully " +
                        "qualified name of class> (1 or more class names)");
                return -1;
            } else if (args[i].equals("-d")) {
                if (i + 1 >= args.length) {
                    System.err.println("No destination folder was specified " +
                            "after -d.");
                    return -1;
                } else {
                    destinationFolder = args[i++];
                }
            } else {
                return i;
            }
        }
        return -1;
    }

    public static void main(String[] args) {
        final int index = processArguments(args);
        if (index == -1) {
            return;
        }
        final MainGenerator mainGenerator = new MainGenerator();
        for (int i = index; i < args.length; i++) {
            final String fullyQualifiedName = args[i];
            try {
                mainGenerator.generate(fullyQualifiedName);
            } catch (ClassNotFoundException e) {
                System.err.println("Class " + fullyQualifiedName + " was not found.");
            }
        }
    }
}
