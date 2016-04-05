package com.tabster.test;

import java.util.ArrayList;

import org.junit.Assert;
import org.junit.Test;

import com.tabster.SMTFunction;
import com.tabster.TabsterService;
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
		final boolean isComplete = !TabsterService.determineTabularExpressionCompleteness(tabularExpression, expressionVars).isSat();
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
		final boolean isDisjoint = !TabsterService.determineTabularExpressionDisjointness(tabularExpression, expressionVars).isSat();
		Assert.assertTrue(isDisjoint == true);
	}
	
	@Test
	public void testSimpleIncompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 5");
		tabularExpression.add("x < 5");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		SMTModel model = TabsterService.determineTabularExpressionCompleteness(tabularExpression, expressionVars);
		final boolean isComplete = !model.isSat();
		Assert.assertTrue(isComplete == false);
		Assert.assertTrue(model.getFunctions().get(0).getValue().equals("5"));
	}
	

	@Test
	public void testSimpleNonDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("x > 5");
		tabularExpression.add("x < 5");
		tabularExpression.add("x < 8");   
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		SMTModel model = TabsterService.determineTabularExpressionDisjointness(tabularExpression, expressionVars);
		final boolean isDisjoint = !model.isSat();
		Assert.assertTrue(isDisjoint == false);
		Assert.assertTrue(model.getFunctions().get(0).getValue().equals("0"));
	}
	
	@Test
	public void testComplexCompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("{∃x:(x > 5)}"); 
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		final boolean isComplete = !TabsterService.determineTabularExpressionCompleteness(tabularExpression, expressionVars).isSat();
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
		SMTModel model = TabsterService.determineTabularExpressionDisjointness(tabularExpression, expressionVars);
		final boolean isDisjoint = !model.isSat();
		Assert.assertTrue(isDisjoint == false);
		Assert.assertTrue(model.getFunctions().get(0).getValue().equals("5"));
		Assert.assertTrue(model.getFunctions().get(1).getValue().equals("true"));
	}
	
	@Test
	public void testComplexDisjointTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("((x > 5) && (y = false))");
		tabularExpression.add("((x <= 5) || (y = true))");  
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
		SMTModel model = TabsterService.determineTabularExpressionDisjointness(tabularExpression, expressionVars);
		final boolean isDisjoint = !model.isSat();
		Assert.assertTrue(isDisjoint == true);
	}
	
	@Test
	public void testComplexIncompleteTabularExpression() throws Exception {
		final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
		final ArrayList<String> tabularExpression = new ArrayList<String>();
		tabularExpression.add("{∀x:(x > 5)}"); 
		expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
		SMTModel model = TabsterService.determineTabularExpressionCompleteness(tabularExpression, expressionVars);
		final boolean isComplete = !model.isSat();
		Assert.assertTrue(isComplete == false);
		Assert.assertTrue(model.getFunctions().get(0).getValue().equals("0"));
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
        SMTModel model = TabsterService.determineTabularExpressionCompleteness(expressions, expressionVars);
        Assert.assertTrue(model.isSat());
        model = TabsterService.determineTabularExpressionDisjointness(expressions, expressionVars);
        Assert.assertTrue(!model.isSat());
		
	}
}
