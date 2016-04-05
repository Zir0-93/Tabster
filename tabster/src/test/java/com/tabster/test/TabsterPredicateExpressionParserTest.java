package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.SMTFunction.FunctionType;
import com.tabster.TabsterService;

/**
 * Tests Tabster's ability to parse and generate accurate SMT-LIB Descriptions
 * from Strings representing tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public class TabsterPredicateExpressionParserTest {

    @Test
    public void testParsingExpressionWithMixedVarTypes() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "((x > 5) || (x - 3) > 6) && false = y && 3.77 < z";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
        expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Bool) (declare-fun z () Real)  (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) (< 3.77 z ) ) ) (check-sat) (get-model) (exit)"));
    }
    
    @Test
    public void testParsingExpressionWithFormalLogicSymbols() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "((x > 5) ∨ (x - 3) > 6) ∧ false = y ∧ 3.77 < z";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
        expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Bool) (declare-fun z () Real)  (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) (< 3.77 z ) ) ) (check-sat) (get-model) (exit)"));
    }     
    
    @Test
    public void testParsingExpressionWithNotSymbol() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "!(x > 5 & !(y < 5)) ∨ !(z)";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.REAL));
        expressionVars.add(new SMTFunction("z", null, FunctionType.BOOL));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Real) (declare-fun z () Bool)  (assert (or (not (and (> x 5 ) (not (< y 5 ) ) ) ) (not z ) ) ) (check-sat) (get-model) (exit)"));
    } 
    @Test
    public void testParsingExpressionWithExistentialQuantifierSymbols() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "{∃x:(x > 5)}";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int)  (assert (exists ((x Int)) (> x 5 ) ) ) (check-sat) (get-model) (exit)"));
    }
    
    @Test
    public void testParsingExpressionWithUniversalQuantifierSymbols() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "{∀x:(x > 5)}";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int)  (assert (forall ((x Int)) (> x 5 ) ) ) (check-sat) (get-model) (exit)"));
    }
    
    @Test
    public void testParsingExpressionWithNestedQuantifierExpression() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "{∃x:{∃y:(x > y)}}";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.INT));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Int)  (assert (exists ((x Int)) (exists ((y Int)) (> x y ) ) ) ) (check-sat) (get-model) (exit)"));
    }
    
    
    @Test
    public void testParsingExpressionWithNegativeIntegers() throws Exception {
    	final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final String unparsedExpression = "!(x > -5 & !(y < -2)) ∨ !(z)";
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.REAL));
        expressionVars.add(new SMTFunction("z", null, FunctionType.BOOL));
        final String smtLibDescription = TabsterService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars, true, true);
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Real) (declare-fun z () Bool)  (assert (or (not (and (> x -5 ) (not (< y -2 ) ) ) ) (not z ) ) ) (check-sat) (get-model) (exit)"));
    } 
}