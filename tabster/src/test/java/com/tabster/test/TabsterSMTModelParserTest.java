package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.TabularExpressionService;

/**
 * Tests to ensure correct parsing and evaluation of SMT-LIB model output.
 *
 * @author Muntazir Fadhel
 */
public class TabsterSMTModelParserTest {

    @Test
    public void testParseGeneralSMTModelExpression() throws Exception {

        final SMTFunction x = new SMTFunction("x", "57", "Integer");
        final ArrayList<SMTFunction> expectedResult = new ArrayList<SMTFunction>();
        expectedResult.add(x);
        final String unparsedExpression = "sat (model (define-fun x () Int 57) )";
        final ArrayList<SMTFunction> functions = TabularExpressionService.extractModelFunctions(unparsedExpression);
        final boolean pass = true;
        for (int i = 0; i < functions.size(); i++) {
            if (!functions.get(i).isEqual(expectedResult.get(i))) {
            }
        }
        Assert.assertTrue(pass);
    }

    @Test
    public void testParseGeneralSMTModelExpressionMultipleFunctions() throws Exception {

        final SMTFunction x = new SMTFunction("x", "0", "Real");
        final SMTFunction y = new SMTFunction("y", "0", "Int");
        final SMTFunction z = new SMTFunction("z", "false", "Bool");
        final ArrayList<SMTFunction> expectedResult = new ArrayList<SMTFunction>();
        expectedResult.add(x);
        expectedResult.add(y);
        expectedResult.add(z);
        final String unparsedExpression = "sat (model (define-fun x () Real 0) (define-fun z () Bool false) (define-fun y () Int 0) )";
        final ArrayList<SMTFunction> functions = TabularExpressionService.extractModelFunctions(unparsedExpression);
        final boolean pass = true;
        for (int i = 0; i < functions.size(); i++) {
            if (!functions.get(i).isEqual(expectedResult.get(i))) {
            }
        }
        Assert.assertTrue(pass);
    }
}
