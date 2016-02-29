package com.tabster.expression;

import expression.TabularExpressionBaseListener;
import expression.TabularExpressionParser;

/**
 * Once the parsing has done it�s job we�ll get ANTLR to walk the grammar and
 * attach a listener � the listener is notified when any one of our parsing
 * rules is triggered. We can use these listeners to build an appropriate
 * SMT-LIB Description of the given tabular expression in order to pass to any
 * SMT-LIB v2 compliant SMT solver
 *
 * @author Muntazir Fadhel
 */
public class TabsterTabularExpressionListener extends TabularExpressionBaseListener {

    private final SMTLIBDescription smtLibDescription;

    /**
     * Public constructor.
     */
    public TabsterTabularExpressionListener(SMTLIBDescription SMTLibDescription) {
        this.smtLibDescription = SMTLibDescription;
    }

    @Override
    public final void enterExpression(final TabularExpressionParser.ExpressionContext ctx) {

        if (!ctx.AND().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.AND().get(0).getText());
        } else if (!ctx.OR().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.OR().get(0).getText());
        }
    }

    @Override
    public final void exitExpression(final TabularExpressionParser.ExpressionContext ctx) {

        if (!ctx.AND().isEmpty() || !ctx.OR().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterRelationalExpression(final TabularExpressionParser.RelationalExpressionContext ctx) {
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
    public final void exitRelationalExpression(final TabularExpressionParser.RelationalExpressionContext ctx) {

        if (!ctx.EQUAL().isEmpty() || !ctx.NOTEQUAL().isEmpty() || !ctx.GT().isEmpty() || !ctx.GE().isEmpty()
                || !ctx.LT().isEmpty() || !ctx.LE().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterAddingExpression(final TabularExpressionParser.AddingExpressionContext ctx) {
        if (!ctx.ADD().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.ADD().get(0).getText());
        } else if (!ctx.SUB().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.SUB().get(0).getText());
        }
    }

    @Override
    public final void exitAddingExpression(final TabularExpressionParser.AddingExpressionContext ctx) {
        if (!ctx.ADD().isEmpty() || !ctx.SUB().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterMultiplyingExpression(final TabularExpressionParser.MultiplyingExpressionContext ctx) {
        if (!ctx.MUL().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.MUL().get(0).getText());
        } else if (!ctx.DIV().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.DIV().get(0).getText());
        } else if (!ctx.MOD().isEmpty()) {
            smtLibDescription.registerExpressionStart(ctx.MOD().get(0).getText());
        }
    }

    @Override
    public final void exitMultiplyingExpression(final TabularExpressionParser.MultiplyingExpressionContext ctx) {
        if (!ctx.MUL().isEmpty() || !ctx.DIV().isEmpty() || !ctx.MOD().isEmpty()) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterSignExpression(final TabularExpressionParser.SignExpressionContext ctx) {
        if (ctx.BANG() != null || ctx.TILDE() != null) {
            smtLibDescription.registerExpressionStart(ctx.BANG().getText());
        }
    }

    @Override
    public final void exitSignExpression(final TabularExpressionParser.SignExpressionContext ctx) {
        if (ctx.BANG() != null || ctx.TILDE() != null) {
            smtLibDescription.registerExpressionEnd();
        }
    }

    @Override
    public final void enterPrimeExpression(final TabularExpressionParser.PrimeExpressionContext ctx) {
        if (ctx.expression() == null) {
            smtLibDescription.registerNewTerm(ctx.getText());
        }
    }

    public SMTLIBDescription getParseResult() {
        return smtLibDescription;
    }
}
