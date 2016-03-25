package com.tabster;

import java.io.Serializable;

/**
 * Represents an input to a predicate expression.
 * @author zir0
 *
 */
public class SMTFunction implements Serializable{

    /**
	 * @param varName the varName to set
	 */
	public void setVarName(String varName) {
		this.varName = varName;
	}
	/**
	 * @param type the type to set
	 */
	public void setType(FunctionType type) {
		this.type = type;
	}

	private String varName = null;
    private String value = null;;
    private FunctionType type = null;

    public SMTFunction() {}
    /**
     * @param varName
     *            Name of the variable
     * @param value
     *            Value of the variable
     * @param type
     *            data type of the variable
     */
    public SMTFunction(final String varName, final String value, final FunctionType type) {
        this.varName = varName;
        this.value = value;
        this.type = type;
    }

    public void setValue(String value) {
		this.value = value;
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
    public FunctionType getType() {
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
    	
    	public String getValue() {
    		return this.value;
    	}    	
    }
}
