package com.tabster.expression;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.apache.commons.io.IOUtils;

import com.tabster.expression.SMTLIBDescription;
import com.tabster.expression.PredicateExpressionListener;
import com.tabster.smtmodel.SMTModel;
import com.tabster.smtmodel.TabsterSMTModelListener;
import com.tabster.SMTFunction;
import com.tabster.SMTScript;

import expression.PredicateExpressionLexer;
import expression.PredicateExpressionParser;
import smtmodel.SMTModelLexer;
import smtmodel.SMTModelParser;

public final class PredicateExpression {
	
	private String predicateExpression;
	private ArrayList<SMTFunction> expressionVars;
	
	public PredicateExpression(String predicateExpression, ArrayList<SMTFunction> expressionVars) {
	    this.predicateExpression = predicateExpression;
	    this.expressionVars = expressionVars;
	}
	
    /**
     * Generates a SMT-LIB v2 compliant script for checking the satisfiability
     * and for getting the model of a given tabular expression.
     *
     * @param tabularExpression
     *            String containing a tabular expression.
     * @param inputs 
     * 		   List containing SMTFunction objects representing variable inputs in the tabular expression.
     * @return String representing the SMT-LIB script input to a SMT solver.
     * @throws Exception
     *             When generating the script encounters an error.
     */
    public String smtLibSolverScript(boolean checkSat, boolean getModel) {
    	String result = null;
    	try {
        SMTLIBDescription description = new SMTLIBDescription(this.expressionVars, this.predicateExpression, checkSat, getModel);
        PredicateExpressionLexer lexer = new PredicateExpressionLexer(new ANTLRInputStream(this.predicateExpression));
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateExpressionParser parser = new PredicateExpressionParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());
        final ParseTree tree = parser.compilationUnit();
        final ParseTreeWalker walker = new ParseTreeWalker();
        PredicateExpressionListener listener = new PredicateExpressionListener(description);
        walker.walk((ParseTreeListener) listener, tree);
        result = listener.parseResult().toString();
    	} catch (ParseCancellationException e) {
    		System.out.println("Error while parsing input expression: " + this.predicateExpression);
    		e.printStackTrace();
    	}
        return result;
    }

    public String solve() throws Exception {

    	String SMTLibString = smtLibSolverScript(true, true);
    	return new SMTScript(SMTLibString).run();
    }
}
