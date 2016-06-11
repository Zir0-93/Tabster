package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.PropertyVerificationResult;
import com.tabster.SMTFunction;
import com.tabster.TabularExpression;
import com.tabster.SMTFunction.FunctionType;
import com.tabster.smtmodel.SMTModel;

public class TabsterTabularExpressionTest {

	@Test
	public void testSimpleCompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 0");
		tabularExpression.add("x < 0");
		tabularExpression.add("x = 0");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		final boolean isComplete = new TabularExpression(tabularExpression,expressionVars).checkCompleteness().satisfied();
		Assert.assertTrue(isComplete == true);
	}
	
	@Test
	public void testSimpleDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 5");
		tabularExpression.add("x < 5");
		tabularExpression.add("x = 5");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		final boolean isDisjoint = new TabularExpression(tabularExpression,expressionVars).checkDisjointness().satisfied();
		Assert.assertTrue(isDisjoint == true);
	}
	
	@Test
	public void testSimpleIncompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 5");
		tabularExpression.add("x < 5");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		PropertyVerificationResult result = new TabularExpression(tabularExpression,expressionVars).checkCompleteness();
		Assert.assertTrue(result.satisfied() == false);
		Assert.assertTrue(result.counterExamples().get(0).value().equals("5"));
	}
	

	@Test
	public void testSimpleNonDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 5");
		tabularExpression.add("x < 5");
		tabularExpression.add("x < 8");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		PropertyVerificationResult result = new TabularExpression(tabularExpression,expressionVars).checkDisjointness(); 
		Assert.assertTrue(result.satisfied() == false);
		Assert.assertTrue(result.counterExamples().get(0).value().equals("0"));
	}
	
	@Test
	public void testComplexCompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("{∃x:(x > 5)}"); 
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		final boolean isComplete = new TabularExpression(tabularExpression,expressionVars).checkCompleteness().satisfied();
		Assert.assertTrue(isComplete == true);
	}
	
	@Test
	public void testComplexNonDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("((x > 5) && (y = false))");
		tabularExpression.add("((x < 5) || (y = true))");
		tabularExpression.add("(x = 5) & ((y = true) | (y = false)) ");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
		PropertyVerificationResult result = new TabularExpression(tabularExpression, expressionVars).checkDisjointness();
		Assert.assertTrue(result.satisfied() == false);
		Assert.assertTrue(result.counterExamples().get(0).value().equals("5"));
		Assert.assertTrue(result.counterExamples().get(1).value().equals("true"));
	}
	
	@Test
	public void testComplexDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("((x > 5) && (y = false))");
		tabularExpression.add("((x <= 5) || (y = true))");  
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
		PropertyVerificationResult result = new TabularExpression(tabularExpression, expressionVars).checkDisjointness();
		Assert.assertTrue(result.satisfied() == false);
	}
	
	@Test
	public void testComplexIncompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("{∀x:(x > 5)}"); 
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		PropertyVerificationResult result = new TabularExpression(tabularExpression, expressionVars).checkCompleteness();
		Assert.assertTrue(result.satisfied() == false);
		Assert.assertTrue(result.counterExamples().get(0).value().equals("0"));
	}
	
	@Test
	public void testLargeIncompleteTabularExpression() throws Exception {
		
        final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
        final ArrayList<String> expressions = new ArrayList<String>();
        expressions.add("((x < 0) & (y = 3))");
        expressions.add("((x < 0) & (y > 3))");
        expressions.add("(x = 0) & (y < 3)");
        expressions.add("(x = 0) & (y = 3)");
        expressions.add("(x = 0) & (y > 3)");
        expressions.add("(x > 0) & (y < 3)");
        expressions.add("(x > 0) & (y = 3)");
        expressions.add("(x > 0) & (y > 3)");
        //expressions.add("(x < 0) & (y < 3)");
        expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
        expressionVars.add(new SMTFunction("y", null, FunctionType.INT));
        PropertyVerificationResult result = new TabularExpression(expressions, expressionVars).completenessModel();
        Assert.assertTrue(result.satisfied());
        result = new TabularExpression(expressions, expressionVars).disjointnessModel();
        Assert.assertTrue(result.satisfied() == false);
		
	}
}
