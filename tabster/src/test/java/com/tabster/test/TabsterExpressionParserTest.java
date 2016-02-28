package com.tabster.test;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.TabularExpressionService;

/**
 * Tests Tabster's ability to parse and generate accurate SMT-LIB Descriptions
 * from Strings representing tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public class TabsterExpressionParserTest {

    @Test
    public void testParseGeneralTabularExpression() throws Exception {

        final String unparsedExpression = "((x > 5) || (x - 3) > 6) && false = y";
        final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals("(declare-fun y () Int) (declare-fun x () Int) (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) ) ) (check-sat) (get-model) (exit)"));
    }

    @Test
    public void testParseRelationalTabularExpression() throws Exception {

        final String unparsedExpression = "(((x > 5) < ((x - 3) > 6)) >= (24 <= 2)) = true";
        final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals(
                        "(declare-fun x () Int) (assert (= (>= (< (> x 5 ) (> (- x 3 ) 6 ) ) (<= 24 2 ) ) true ) ) (check-sat) (get-model) (exit)"));
    }

    @Test
    public void testParseMathTabularExpression() throws Exception {

        final String unparsedExpression = "((x * 5) < ((x - 3) % 6)) >= (24 / 2)";
        final String smtLibDescription = TabularExpressionService.extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals("(declare-fun x () Int) (assert (>= (< (* x 5 ) (mod (- x 3 ) 6 ) ) (/ 24 2 ) ) ) (check-sat) (get-model) (exit)"));
    }

    @Test
    public void testNegationTabularExpression() throws Exception {

        final String unparsedExpression = "!(((x * 5) < ((x - 3) % 6)) >= (24 / 2))";
        final String smtLibDescription = TabularExpressionService.extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals("(declare-fun x () Int) (assert (not (>= (< (* x 5 ) (mod (- x 3 ) 6 ) ) (/ 24 2 ) ) ) ) (check-sat) (get-model) (exit)"));
    }

    @Test
    public void testParseLiteralsInTabularExpression() throws Exception {

        final String unparsedExpression = "x = \"str\" || 4 = false";
        final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals(
                        "(declare-fun x () Int) (assert (or (= x \"str\" ) (= 4 false ) ) ) (check-sat) (get-model) (exit)"));
    }
    @Test
    public void testDeclareUniqueTermOnceOnly() throws Exception {

        final String unparsedExpression = "x  = 3 || x > 4 || x > 10";
        final String smtLibDescription = TabularExpressionService.extractSMTLibSolverScript(unparsedExpression);
        Assert.assertTrue(smtLibDescription
                .equals(
                        "(declare-fun x () Int) (assert (or (= x 3 ) (> x 4 ) (> x 10 ) ) ) (check-sat) (get-model) (exit)"));
    }
}
