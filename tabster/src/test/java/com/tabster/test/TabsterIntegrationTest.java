package com.tabster.test;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.TabularExpressionService;

public class TabsterIntegrationTest {

    @Test
    public void testSolveGeneralTabularExpression() throws Exception {

        final String unparsedExpression = "((x > 5) || (x - 3) > 6) && false = y";
        final String smtLibDescription = TabularExpressionService.extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals("(declare-fun y () Int) (declare-fun x () Int) (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) ) ) (check-sat) (get-model) (exit)"));
    }

}
