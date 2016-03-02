# Tabster
Translates tabular expressions into the [SMT Exchange format](http://smtlib.github.io/jSMTLIB/SMTLIBTutorial.pdf) descriptions which can be used as input to an SMT solver. Tabster can also solve these expressions if CVC4 is installed on your machine.

### Getting Started

#### Converting a Tabular Expression to The SMT Exchange Format
    final ArrayList<SMTFunction> expressionVars = new ArrayList<SMTFunction>();
    // The input: A string representing the tabular expression to be translated
    final String unparsedExpression = "((x > 5) || (x - 3) > 6) && false = y && 3.77 < z";
    // Specify types of the vars used in the expression ...
    expressionVars.add(new SMTFunction("x", null, FunctionType.INT));
    expressionVars.add(new SMTFunction("y", null, FunctionType.BOOL));
    expressionVars.add(new SMTFunction("z", null, FunctionType.REAL));
    final String smtLibDescription = TabularExpressionService
                .extractSMTLibSolverScript(unparsedExpression, expressionVars);
        // The returned String should contain an SMT Lib compliant script to check the satisfiability 
        // and retrieve the model of the given expression
        Assert.assertTrue(smtLibDescription
                .equals("(set-logic AUFLIRA) (set-option :produce-models true) (declare-fun x () Int) (declare-fun y () Bool) (declare-fun z () Real)  (assert (and (or (> x 5 ) (> (- x 3 ) 6 ) ) (= false y ) (< 3.77 z ) ) ) (check-sat) (get-model) (exit)"));
