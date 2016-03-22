package com.tabster;

import java.io.File;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.apache.commons.io.IOUtils;

import com.tabster.expression.SMTLIBDescription;
import com.tabster.expression.TabsterTabularExpressionListener;
import com.tabster.smtmodel.SMTModel;
import com.tabster.smtmodel.TabsterSMTModelListener;

import expression.TabularExpressionLexer;
import expression.TabularExpressionParser;
import smtmodel.SMTModelLexer;
import smtmodel.SMTModelParser;

/**
 * Service class for parsing/solving tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public final class TabularExpressionService {
	
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
    		ArrayList<SMTFunction> expressionVars ) throws Exception {
    	
        SMTLIBDescription description = new SMTLIBDescription(expressionVars, tabularExpression);
        TabularExpressionLexer lexer = new TabularExpressionLexer(new ANTLRInputStream(tabularExpression));
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        TabularExpressionParser parser = new TabularExpressionParser(tokens);
        final ParseTree tree = parser.compilationUnit();
        final ParseTreeWalker walker = new ParseTreeWalker();
        TabsterTabularExpressionListener listener = new TabsterTabularExpressionListener(description);
        walker.walk((ParseTreeListener) listener, tree);
        return listener.getParseResult().toString();
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
    public static ArrayList<SMTFunction> extractModelFunctionsValues(final String smtLibModelOutput,
    ArrayList<SMTFunction> expressionVars) throws Exception {
    	 
    	 SMTModel model = new SMTModel(smtLibModelOutput, expressionVars);
         SMTModelLexer lexer = new SMTModelLexer(new ANTLRInputStream(smtLibModelOutput));
         final CommonTokenStream tokens = new CommonTokenStream(lexer);
         SMTModelParser parser = new SMTModelParser(tokens);
         final ParseTree tree = parser.compilationUnit();
         final ParseTreeWalker walker = new ParseTreeWalker();
         TabsterSMTModelListener listener = new TabsterSMTModelListener(model);
         walker.walk((ParseTreeListener) listener, tree);
         return listener.getParseResult().getFunctions();
    }

    public static void solveTabularExpression(String tabularExpression, ArrayList<SMTFunction> inputs) throws Exception {

    	String response = "";
    	try {
    		String SMTLibString = extractSMTLibSolverScript(tabularExpression, inputs);
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
    		int shellExitStatus = shell.waitFor();
    		if (shellExitStatus != 0) {
    			throw new Exception("Error attempting to determine satisfiability of given tabular expression");
    		}
    		response = IOUtils.toString(shellin, StandardCharsets.UTF_8);
    		shellin.close();        	
    	} catch (Exception e) {
    		System.out.println("Could not process tabular expression: " + tabularExpression);   
    		e.printStackTrace();
    	}
    	// extract the variable solutions from the SMT Lib Model output and return
    	extractModelFunctionsValues(response, inputs);       
    }
    
    
    /**
     * Utility class should not have a public/default constructor.
     */
    private TabularExpressionService() {
    }
}
