package com.tabster.smtmodel;

import java.util.ArrayList;

import com.tabster.AntlrParseResult;
import com.tabster.SMTFunction;

/**
 * Represents the model output of SMTLIB compliant SMT solver.
 *
 * @author Muntazir Fadhel
 */
public class SMTModel implements AntlrParseResult {

    private String smtModelAsString;
    private ArrayList<SMTFunction> functions = new ArrayList<SMTFunction>();

    /**
     * @param functions
     *            the functions to set
     */
    public void setFunctions(final ArrayList<SMTFunction> functions) {
        this.functions = functions;
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
