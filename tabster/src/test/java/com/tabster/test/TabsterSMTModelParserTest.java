package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.TabsterService;
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
        + varXType.getValue() + " " + varXValue + ")(define-fun " + varYNameModelString + " () " 
        		+ varYType.getValue() + " " + varYValue + " )(define-fun " + varZName 
        		+ " () " + varZType.getValue() + " " + varZValueString + ") (define-fun " + varANameModelString 
        		+ " () " + varAType.getValue() + " " + varAStringValue + "))";
       SMTModel model = TabsterService.extractModelFunctionsValues(unparsedExpression, expressionVars);
       expressionVars = model.getFunctions();
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
    public void testParsedRealValueAsDivisionStatementCorrectly() {
    	
    	boolean pass = false;
    	
    	for (SMTFunction var : expressionVars) {
    		if (var.getVarName().equals(varAName)) {
    			if (var.getValue().equals(varAValue)) {
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
