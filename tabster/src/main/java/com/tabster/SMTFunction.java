package com.tabster;

/**
 * Represents an input to a predicate expression.
 * @author zir0
 *
 */
public class SMTFunction {

	private String varName;
    private String value;
    private FunctionType type;

    public SMTFunction(final String varName, final String value, final FunctionType type) {
        this.varName = varName;
        this.value = value;
        this.type = type;
    }

    public final
    String varName() {
        return varName;
    }

    public final
    String value() {
        return value;
    }

    @Override
    public final String toString() {
        return varName + "=" + value;
    }

    public FunctionType type() {
        return type;
    }

    /**
     * @param var
     *            SMTFunction object whose equivalence with the current
     *            SMTFunction object is being compared.
     * @return true when the two objects are equal, false otherwise.
     */
    public boolean isEqual(final SMTFunction var) {

        if (var.type().equals(type) && var.value().equals(value) && var.varName().equals(varName)) {
            return true;
        }
        return false;
    }
    
    public enum FunctionType {
    	
    	BOOL("Bool"),
    	INT("Int"),
    	REAL("Real");
    	
    	private String value = "";
    	
    	private FunctionType() {
    		
    	}
    	
    	private FunctionType(String value) {
			this.value = value;
		}
    	
    	public String value() {
    		return this.value;
    	}    	
    }

	public void setValue(String value) {
		this.value = value;
		
	}
}
