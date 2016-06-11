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

    private ArrayList<SMTFunction> functions = new ArrayList<SMTFunction>();
	private boolean sat;

    public SMTModel(String SMTModelOutput, ArrayList<SMTFunction> expressionVars) {
    	
    	
    /**
     * Extracts the SMT-LIB functions from a String representing SMT-LIB Model
     * Output.
     */

 this.functions = expressionVars;
    	 
    	SMTModel result = null;
    	try {
    	 SMTModel model = new SMTModel(SMTModelOutput, expressionVars);
         SMTModelLexer lexer = new SMTModelLexer(new ANTLRInputStream(SMTModelOutput));
         final CommonTokenStream tokens = new CommonTokenStream(lexer);
         SMTModelParser parser = new SMTModelParser(tokens);
         final ParseTree tree = parser.compilationUnit();
         parser.setErrorHandler(new BailErrorStrategy());
         final ParseTreeWalker walker = new ParseTreeWalker();
         TabsterSMTModelListener listener = new TabsterSMTModelListener(this);
         walker.walk((ParseTreeListener) listener, tree);
    	 result = listener.getParseResult();
    	} catch (Exception e) {
    		System.out.println("Could not process input SMT model string, are you sure it is well-formatted?");
    		e.printStackTrace();
    	}   	
    }
    
	public boolean sat() {
		return sat;
	}
	
	public void setSat(boolean sat) {
	    this.sat = sat;
	}

    public ArrayList<SMTFunction> functions() {
        return functions;
    }
    
    public void insertFunction(final SMTFunction function) {
        functions.add(function);
    }
}
