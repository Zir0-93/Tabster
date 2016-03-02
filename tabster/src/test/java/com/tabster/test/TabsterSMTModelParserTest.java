package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.TabularExpressionService;
import com.tabster.SMTFunction.FunctionType;

/**
 * Tests to ensure correct parsing and evaluation of SMT-LIB model output.
 *
 * @author Muntazir Fadhel
 */
public class TabsterSMTModelParserTest {

	private static ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
	
	private static String varXName = "x";
	private static FunctionType varXType = FunctionType.INT;
	private static String varXValue = "6";
	
	private static String varZName = "z";
	private static FunctionType varZType = FunctionType.REAL;
	private static String varZValue = "5";
	
	private static String varYName = "y";
	private static FunctionType varYType = FunctionType.BOOL;
	private static String varYValue = "false";
    
	
	@BeforeClass
    public static void testParseGeneralSMTModelExpression() throws Exception {

        expressionVars.add(new SMTFunction(varXName, null, varXType));
        expressionVars.add(new SMTFunction(varYName, null, varYType));
        expressionVars.add(new SMTFunction(varZName, null, varZType));
        final String unparsedExpression = "sat (model(define-fun " + varXName + " () "
        + varXType.getValue() + " " + varXValue + ")(define-fun " + varYName + " () " 
        		+ varYType.getValue() + " " + varYValue + " )(define-fun " + varZName 
        		+ " () " + varZType.getValue() + " " + varZValue + "))";
        TabularExpressionService.extractModelFunctionsValues(unparsedExpression, expressionVars);
    }
    
    @Test
    public void testParsedIntValueCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.getVarName().equals(varXName)) {
    			if (var.getValue().equals(varXValue)) {
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
    		if (var.getVarName().equals(varXName)) {
    			if (var.getType().getValue().equals(varXType.getValue())) {
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
    		if (var.getVarName().equals(varZName)) {
    			if (var.getValue().equals(varZValue)) {
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
    		if (var.getVarName().equals(varZName)) {
    			if (var.getType().getValue().equals(varZType.getValue())) {
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
    		if (var.getVarName().equals(varYName)) {
    			if (var.getValue().equals(varYValue)) {
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
    		if (var.getVarName().equals(varYName)) {
    			if (var.getType().getValue().equals(varYType.getValue())) {
    				pass = true;
    			}
    		}
    	}
    	Assert.assertTrue(pass);
    }
}
