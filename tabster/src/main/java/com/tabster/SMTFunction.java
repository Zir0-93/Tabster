package com.tabster;


/**
 * Represents an input to a predicate expression.
 * @author zir0
 *
 */
public class SMTFunction {

    private final String varName;
    private final String value;
    private final String type;

    /**
     * @param varName
     *            Name of the variable
     * @param value
     *            Value of the variable
     * @param type
     *            data type of the variable
     */
    public SMTFunction(final String varName, final String value, final String type) {
        this.varName = varName;
        this.value = value;
        this.type = type;
    }

    /**
     * @return name of the variable
     */
    public final
    String getVarName() {
        return varName;
    }

    /**
     * @return value of the variable
     */
    public final
    String getValue() {
        return value;
    }

    @Override
    public final String toString() {
        return varName + "=" + value;
    }

    /**
     * @return the type of the variable
     */
    public String getType() {
        return type;
    }

    /**
     * @param var
     *            SMTFunction object whose equivalence with the current
     *            SMTFunction object is being compared.
     * @return true when the two objects are equal, false otherwise.
     */
    public boolean isEqual(final SMTFunction var) {

        if (var.getType().equals(type) && var.getValue().equals(value) && var.getVarName().equals(varName)) {
            return true;
        }
        return false;
    }
}
