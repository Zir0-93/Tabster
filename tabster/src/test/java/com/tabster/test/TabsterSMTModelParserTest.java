package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.SMTFunction.FunctionType;
import com.tabster.smtmodel.SMTModel;

/**
 * Tests to ensure correct parsing and evaluation of SMT-LIB model output.
 *
 * @author Muntazir Fadhel
 */
public class TabsterSMTModelParserTest {

	private static ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
	
	private static String varXName = "x";
	private static FunctionType varXType = FunctionType.INT;
	private static String varXValue = "(- 6)";
	
	private static String varZName = "z";
	private static FunctionType varZType = FunctionType.REAL;
	private static String varZValueString = "(/ 477.0 100.0)";
	private static String varZValue = "4.77";
	
	private static String varYNameModelString = "y!0";
	private static String varYName = "y";
	private static FunctionType varYType = FunctionType.BOOL;
	private static String varYValue = "false";
    
	private static String varANameModelString = "a!1";
	private static String varAName = "a";
	private static FunctionType varAType = FunctionType.INT;
	private static String varAStringValue = "(/ 477.0 100.0)";
	private static String varAValue = "4";
	
	@BeforeClass
    public static void testParseGeneralSMTModelExpression() throws Exception {

        expressionVars.add(new SMTFunction(varXName, null, varXType));
        expressionVars.add(new SMTFunction(varYName, null, varYType));
        expressionVars.add(new SMTFunction(varZName, null, varZType));
        expressionVars.add(new SMTFunction(varAName, null, varAType));
        
        final String unparsedExpression = "sat (model(define-fun " + varXName + " () "
        + varXType.value() + " " + varXValue + ")(define-fun " + varYNameModelString + " () " 
        		+ varYType.value() + " " + varYValue + " )(define-fun " + varZName 
        		+ " () " + varZType.value() + " " + varZValueString + ") (define-fun " + varANameModelString 
        		+ " () " + varAType.value() + " " + varAStringValue + "))";
       expressionVars = new SMTModel(unparsedExpression, expressionVars).functions();
    }
    
    @Test
    public void testParsedIntValueCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varXName)) {
    			if (var.value().equals(varXValue)) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedIntTypeCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varXName)) {
    			if (var.type().value().equals(varXType.value())) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedRealValueCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varZName)) {
    			if (var.value().equals(varZValue)) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedRealValueAsDivisionStatementCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varAName)) {
    			if (var.value().equals(varAValue)) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedRealTypeCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varZName)) {
    			if (var.type().value().equals(varZType.value())) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedBoolValueCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varYName)) {
    			if (var.value().equals(varYValue)) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
    
    @Test
    public void testParsedBoolTypeCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.varName().equals(varYName)) {
    			if (var.type().value().equals(varYType.value())) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
}
