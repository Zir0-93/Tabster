# tabster

[Explore Tabster](http://clarityviews.ca:9080/github/java/zir0-93/tabster)

Translates predicate expressions into the [SMT Exchange format](http://smtlib.github.io/jSMTLIB/SMTLIBTutorial.pdf) descriptions using ANTLRv4 Tree Listeners which can be used as input to an SMT solver. Tabster can also solve these expressions if CVC4 is installed on your machine.

### Getting Started
Import Tabster jar from /target folder. To build, run a maven build using goals:"clean compile assembly:single", this should produce the jar in the /target folder. Moving artifacts to maven soon.

#### Converting a Tabular Expression to The SMT Exchange Format
```java
    final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
    // The input: A string representing the tabular expression to be translated
    final String unparsedExpression = "{∃x:((x > 5) || (x - 3) > 6) && false = y && 3.77 < z}";
    // Specify types of the vars used in the expression ...
    expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
    expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
    expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
    final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars);
        // The returned String should contain an SMT Lib compliant script to check the satisfiability 
        // and retrieve the model of the given expression
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Bool) (declare-fun z () Real)  (assert (exists ((x Int)) (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) (< 3.77 z ) ) ) ) (check-sat) (get-model) (exit)"));
```
#### Parsing SMT Exchange Model Ouput
```java
   // Scenario: SMT solver has returned output in the SMT Exchange form.
   String smtModelOutput = "sat (model (define-fun x () Int 6) (define-fun y () Bool false ) (define-fun z () Real 5))";
   // Specify types of the vars used in the expression ...
    expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
    expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
    expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
   // Process the output, populates the expression variables with values
   TabularExpressionService.extractModelFunctionsValues(smtModelOutput, expressionVars);
   System.out.println(expressionVars.get(0).getValue(); // -> "6"
   System.out.println(expressionVars.get(1).getValue(); // -> "false"
   System.out.println(expressionVars.get(2).getValue(); // -> "5"
```
