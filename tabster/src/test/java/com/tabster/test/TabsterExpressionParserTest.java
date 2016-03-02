package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.SMTFunction.FunctionType;
import com.tabster.TabularExpressionService;

/**
 * Tests Tabster's ability to parse and generate accurate SMT-LIB Descriptions
 * from Strings representing tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public class TabsterExpressionParserTest {

    @Test
    public void testParsingExpressionWithMixedVarTypes() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "((x > 5) || (x - 3) > 6) && false = y && 3.77 < z";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
        expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
        final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Bool) (declare-fun z () Real)  (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) (< 3.77 z ) ) ) (check-sat) (get-model) (exit)"));
    }    
}