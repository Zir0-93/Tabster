package com.tabster.expression;

import expression.PredicateExpressionBaseListener;
import expression.PredicateExpressionBaseListener;
import expression.PredicateExpressionParser;

/**
 * Once the parsing has done it�s job we�ll get ANTLR to walk the grammar and
 * attach a listener � the listener is notified when any one of our parsing
 * rules is triggered. We can use these listeners to build an appropriate
 * SMT-LIB Description of the given Predicate expression in order to pass to any
 * SMT-LIB v2 compliant SMT solver
 *
 * @author Muntazir Fadhel
 */
public class PredicateExpressionListener extends PredicateExpressionBaseListener {

    private final SMTLIBDescription smtLibDescription;

    /**
     * Public constructor.
     */
    public PredicateExpressionListener(SMTLIBDescription SMTLibDescription) {
        this.smtLibDescription = SMTLibDescription;
    }

    @Override
    public final void enterExpression(final PredicateExpressionParser.ExpressionContext ctx) {

        if (!ctx.andsign().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.andsign().get(0).getText());
        } else if (!ctx.orsign().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.orsign().get(0).getText());
        } else if(ctx.notsign() != null) {
        	smtLibDescription.registerExpressionStart(ctx.notsign().getText());
        }
    }

    @Override
    public final void exitExpression(final PredicateExpressionParser.ExpressionContext ctx) {

        if (!ctx.andsign().isEmpty() || !ctx.orsign().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }
    @Override
    public final void exitPredicateExpression(final PredicateExpressionParser.PredicateExpressionContext ctx) {

    	smtLibDescription.registerExpressionEnd();
    }

    @Override
    public final void enterPredicateSymbolVariablePair(final PredicateExpressionParser.PredicateSymbolVariablePairContext ctx) {

    	try {
    		if (ctx.FORALL() != null) {
    			smtLibDescription.registerPredicateExpressionStart(ctx.FORALL().getText(), ctx.variable().getText());

    		} if (ctx.EXISTS() != null) {
    			smtLibDescription.registerPredicateExpressionStart(ctx.EXISTS().getText(), ctx.variable().getText());
    		}
    	} catch (Exception e) {
    		e.printStackTrace();
    	}
    }

    @Override
    public final void enterRelationalExpression(final PredicateExpressionParser.RelationalExpressionContext ctx) {
        if (!ctx.EQUAL().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.EQUAL().get(0).getText());
        } else if (!ctx.NOTEQUAL().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.NOTEQUAL().get(0).getText());
        } else if (!ctx.GT().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.GT().get(0).getText());
        } else if (!ctx.GE().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.GE().get(0).getText());
        } else if (!ctx.LT().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.LT().get(0).getText());
        } else if (!ctx.LE().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.LE().get(0).getText());
        }
    }

    @Override
    public final void exitRelationalExpression(final PredicateExpressionParser.RelationalExpressionContext ctx) {

        if (!ctx.EQUAL().isEmpty() || !ctx.NOTEQUAL().isEmpty() || !ctx.GT().isEmpty() || !ctx.GE().isEmpty()
                || !ctx.LT().isEmpty() || !ctx.LE().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterAddingExpression(final PredicateExpressionParser.AddingExpressionContext ctx) {
        if (!ctx.ADD().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.ADD().get(0).getText());
        } else if (!ctx.SUB().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.SUB().get(0).getText());
        }
    }

    @Override
    public final void exitAddingExpression(final PredicateExpressionParser.AddingExpressionContext ctx) {
        if (!ctx.ADD().isEmpty() || !ctx.SUB().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterMultiplyingExpression(final PredicateExpressionParser.MultiplyingExpressionContext ctx) {
        if (!ctx.MUL().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.MUL().get(0).getText());
        } else if (!ctx.DIV().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.DIV().get(0).getText());
        } else if (!ctx.MOD().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.MOD().get(0).getText());
        }
    }

    @Override
    public final void exitMultiplyingExpression(final PredicateExpressionParser.MultiplyingExpressionContext ctx) {
        if (!ctx.MUL().isEmpty() || !ctx.DIV().isEmpty() || !ctx.MOD().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void exitSignExpression(final PredicateExpressionParser.SignExpressionContext ctx) {
        if (ctx.BANG() != null || ctx.TILDE() != null) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterSignExpression(final PredicateExpressionParser.SignExpressionContext ctx) {
        if (ctx.primeExpression().expression() == null) {
            smtLibDescription.registerNewTerm(ctx.getText());
        } else {
        	if (ctx.BANG() != null || ctx.TILDE() != null) {
                smtLibDescription.registerExpressionStart(ctx.BANG().getText());
            }
        }
    }

    public SMTLIBDescription parseResult() {
        return smtLibDescription;
    }
}
