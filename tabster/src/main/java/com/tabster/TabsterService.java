package com.tabster;

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

import expression.PredicateExpressionLexer;
import expression.PredicateExpressionParser;
import smtmodel.SMTModelLexer;
import smtmodel.SMTModelParser;

/**
 * Service class for parsing/solving tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public final class TabsterService {
	
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
    public static String extractSMTLibSolverScript(final String tabularExpression, 
    		ArrayList<SMTFunction> expressionVars, boolean checkSat, boolean getModel) {
    	String result = null;
    	try {
        SMTLIBDescription description = new SMTLIBDescription(expressionVars, tabularExpression, checkSat, getModel);
        PredicateExpressionLexer lexer = new PredicateExpressionLexer(new ANTLRInputStream(tabularExpression));
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        PredicateExpressionParser parser = new PredicateExpressionParser(tokens);
        parser.setErrorHandler(new BailErrorStrategy());
        final ParseTree tree = parser.compilationUnit();
        final ParseTreeWalker walker = new ParseTreeWalker();
        PredicateExpressionListener listener = new PredicateExpressionListener(description);
        walker.walk((ParseTreeListener) listener, tree);
        result = listener.getParseResult().toString();
    	} catch (ParseCancellationException e) {
    		System.out.println("Error while parsing input expression:: " + tabularExpression);
    		e.printStackTrace();
    	}
        return result;
    }

    /**
     * Extracts the SMT-LIB functions from a String representing SMT-LIB Model
     * Output.
     *
     * @param smtLibModelOutput
     *            String containing SMT-LIB model output
     * @return List of SMT Functions representing the model functions
     * @throws Exception
     *             When an error is encountered during the extraction process.
     */
    public static SMTModel extractModelFunctionsValues(final String smtLibModelOutput,
    ArrayList<SMTFunction> expressionVars) {
    	 
    	SMTModel result = null;
    	try {
    	 SMTModel model = new SMTModel(smtLibModelOutput, expressionVars);
         SMTModelLexer lexer = new SMTModelLexer(new ANTLRInputStream(smtLibModelOutput));
         final CommonTokenStream tokens = new CommonTokenStream(lexer);
         SMTModelParser parser = new SMTModelParser(tokens);
         final ParseTree tree = parser.compilationUnit();
         parser.setErrorHandler(new BailErrorStrategy());
         final ParseTreeWalker walker = new ParseTreeWalker();
         TabsterSMTModelListener listener = new TabsterSMTModelListener(model);
         walker.walk((ParseTreeListener) listener, tree);
    	 result = listener.getParseResult();
    	} catch (Exception e) {
    		System.out.println("Could not process input SMT model string, are you sure it is well-formatted?");
    		e.printStackTrace();
    	}
         return result;
    }

    public static void solvePredicateExpression(String tabularExpression, ArrayList<SMTFunction> inputs) throws Exception {

    	String SMTLibString = extractSMTLibSolverScript(tabularExpression, inputs, true, true);
    	String response = runSMTScript(SMTLibString, inputs);
    	// extract the variable solutions from the SMT Lib Model output and return
    	extractModelFunctionsValues(response, inputs);       
    }
    
    private static String runSMTScript (String SMTLibString, ArrayList<SMTFunction> expressionVars) throws Exception {
    	// create a temp file    	
    	File f = File.createTempFile("smt", ".smt2");
    	PrintWriter writer = new PrintWriter(f);
    	writer.print(SMTLibString);
    	writer.close();
    	// interact with terminal to check satisfiability and solve SMT Lib String
    	String command = "z3 -smt2 " + f.getAbsolutePath();
    	ProcessBuilder pb = new ProcessBuilder("bash", "-c", command);
    	pb.redirectErrorStream(true);
    	Process shell = pb.start();
    	// To capture output from shell
    	InputStream shellin = shell.getInputStream();
    	// Wait for shell to finish and get the return code
    	shell.waitFor();
    	String response = IOUtils.toString(shellin, StandardCharsets.UTF_8);
    	shellin.close();  
    	return response;
    }

    /**
     * The given tabular expression is complete when the returned model
     * is not satisfiable, otherwise the expression is incomplete. If the 
     * expression is incomplete, the values of the SMTFunctions within the
     * model will include counter examples.
     */
    public static SMTModel determineTabularExpressionCompleteness(ArrayList<String> tabularExpression, ArrayList<SMTFunction> expressionVars) throws Exception {

    	// to check for completion, check if the following expression is satisfiable:
    	String completionCheckExpression = "";
    	for (String predExpr : tabularExpression) {
    		completionCheckExpression += "!(" + predExpr + ") ∧ ";
    	}
    	// remove the last LOGICAL AND
    	completionCheckExpression = completionCheckExpression.substring(0, completionCheckExpression.length() - 2);
    	String SMTLibString = extractSMTLibSolverScript(completionCheckExpression, expressionVars, true, true);
    	String scriptResult = runSMTScript(SMTLibString, expressionVars);
    	SMTModel model = extractModelFunctionsValues(scriptResult, expressionVars);
    	return model;
    }

    /**
     * If the returned model is satisfiable, the given expression are
     * not disjoint. In this case the returned SMTFunctions will show counter
     * examples. If the model is not satisfiable, then the given tabular
     * expressions is disjoint.
     */
    public static SMTModel determineTabularExpressionDisjointness(ArrayList<String> tabularExpression, ArrayList<SMTFunction> expressionVars) throws Exception {
    	// The basic strategy to determine disjointness is to ensure that no two condition rows
    	// in the table when AND'ed together are satisifiable.
    	for (int i = tabularExpression.size() - 1; i > 0; i --) {
    		for (int j = i - 1; j >= 0; j --) {
    			String checkExpression = tabularExpression.get(i) + " ∧ " + tabularExpression.get(j);
    			// if the problem is satisfiable, that is, the returned input variables have values, the tabular
    			// expression is not complete
    			String SMTLibString = extractSMTLibSolverScript(checkExpression, expressionVars, true, true);
    			String scriptResult = runSMTScript(SMTLibString, expressionVars);
    			SMTModel model = extractModelFunctionsValues(scriptResult, expressionVars);
    			if (model.isSat()) {
    				return model;
    			}
    		}
    	}
    	// expressions are disjoint!
    	SMTModel disjointModel = new SMTModel();
    	disjointModel.setFunctions(expressionVars);
    	disjointModel.setSat(false);
    	return disjointModel;
    }

    /**
     * Utility class should not have a public/default constructor.
     */
    private TabsterService() {
    }
}
