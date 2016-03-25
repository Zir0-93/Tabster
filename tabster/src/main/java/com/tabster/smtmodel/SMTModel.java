package com.tabster.smtmodel;

import java.io.Serializable;
import java.util.ArrayList;

import com.tabster.SMTFunction;

/**
 * Represents the model output of SMTLIB compliant SMT solver.
 *
 * @author Muntazir Fadhel
 */
public class SMTModel implements Serializable{

    private String smtModelAsString;
    private ArrayList<SMTFunction> functions = new ArrayList<SMTFunction>();
	private boolean sat;

    public SMTModel(String SMTModelOutput, ArrayList<SMTFunction> expressionVars) {
    	this.smtModelAsString = SMTModelOutput;
    	this.functions = expressionVars;
    }
    
    public SMTModel() {}
    /**
     * @param functions
     *            the functions to set
     */
    public void setFunctions(final ArrayList<SMTFunction> functions) {
        this.functions = functions;
    }
    
	/**
	 * @return the sat
	 */
	public boolean isSat() {
		return sat;
	}

	/**
	 * @param sat the sat to set
	 */
	public void setSat(boolean sat) {
		this.sat = sat;
	}

    /**
     * @return the functions
     */
    public ArrayList<SMTFunction> getFunctions() {
        return functions;
    }

    /**
     * @return the sMTModelAsString
     */
    public String getSMTModelAsString() {
        return smtModelAsString;
    }

    /**
     * @param sMTModelAsString the sMTModelAsString to set
     */
    public void setSMTModelAsString(final String sMTModelAsString) {
        smtModelAsString = sMTModelAsString;
    }

    /**
     * Insert a new SMT function into the current model.
     *
     * @param function
     *            function to insert
     */
    public void insertFunction(final SMTFunction function) {
        functions.add(function);

    }
}
