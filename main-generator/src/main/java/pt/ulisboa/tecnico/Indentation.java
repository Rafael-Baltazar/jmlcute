package pt.ulisboa.tecnico;

/**
 * Implements indentation in MainGenerator.
 *
 * @see MainGenerator
 */
public class Indentation {
    private String indentation = "";
    private final String indentationElement;

    public Indentation() {
        indentationElement = "  ";
    }

    public Indentation(String indentationElement) {
        this.indentationElement = indentationElement;
    }

    /**
     * Increase the indentation by indentationIncrease.
     *
     * @param indentationIncrease the amount of indentation to increase. Has
     *                            to be positive.
     */
    public void increase(int indentationIncrease) {
        StringBuilder sb = new StringBuilder(indentation);
        for (int i = 0; i < indentationIncrease; i++) {
            sb.append(indentationElement);
        }
        indentation = sb.toString();
    }

    /**
     * Increase by one.
     */
    public void increase() {
        increase(1);
    }

    /**
     * Decreases the indentation by indentationDecrease, if the current
     * indentation is greater or equal than indentationDecrease.
     *
     * @param indentationDecrease the amount of indentation to decrease. Has
     *                            to be positive.
     * @return true, if the indentation was decreased. Otherwise, false.
     */
    public boolean decrease(int indentationDecrease) {
        if (indentationDecrease > indentation.length()) {
            return false;
        }
        indentation = indentation.substring(0, indentation.length() -
                (indentationDecrease * indentationElement.length()));
        return true;
    }

    /**
     * Decrease by one.
     *
     * @return true, if indentation was decreased. Otherwise, false.
     */
    public boolean decrease() {
        return decrease(1);
    }

    @Override
    public String toString() {
        return indentation;
    }
}
