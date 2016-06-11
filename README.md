# :rocket: tabster

[![Clarity Views Label](http://clarityviews.ca/badge)](http://clarityviews.ca/github/clarity-team/tabster?projectName=tabster)

Tabster is an object oriented library used for verifying properties of tabular expressions such as completeness and disjointness through the use of SMT solvers. When a given property is not satisfied, Tabster returns counter examples to highlight the situation in which the property fails to hold.

### Getting Started
Ensure the z3 SMT Solver is installed on your machine, see instructions [here](https://github.com/Z3Prover/z3). To build the project, run a maven build using goals:"clean package assembly:single" - this should generate the ANTLR dependencies and generate the Tabster jar in the /target folder. Or download the latest stable version of the jar from the [releases](https://github.com/Zir0-93/tabster/releases) page.

### Using the API
An excellent way to get started is to look at Tabster's unit tests.

#### Determining completeness of a tabular expression.
```java
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
```
#### Determining Disjointness of a tabular expression
```java
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
```
