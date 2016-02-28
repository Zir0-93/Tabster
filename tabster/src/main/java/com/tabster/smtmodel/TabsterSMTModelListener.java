package com.tabster.smtmodel;

import smtmodel.SMTModelBaseListener;
import smtmodel.SMTModelParser;

import com.tabster.AntlrParseResult;
import com.tabster.ITabsterANTLRParseTreeListener;
import com.tabster.SMTFunction;
import com.tabster.expression.AntlrUtil;

/**
 * Once the parsing has done it’s job we’ll get ANTLR to walk the grammar and
 * attach a listener – the listener is notified when any one of our parsing
 * rules is triggered. We can use these listeners to build an appropriate
 * SMT-LIB Description of the given tabular expression in order to pass to any
 * SMT-LIB v2 compliant SMT solver.
 *
 * @author Muntazir Fadhel
 */
public class TabsterSMTModelListener extends SMTModelBaseListener implements ITabsterANTLRParseTreeListener {

    private final SMTModel model;

    /**
     * Public constructor.
     */
    public TabsterSMTModelListener() {
        model = new SMTModel();
    }

    @Override
    public final void enterFunctionDeclaration(final SMTModelParser.FunctionDeclarationContext ctx) {

        final SMTFunction var = new SMTFunction(ctx.varName().getText(), ctx.varValue().getText(), ctx.varType().getText());
        model.insertFunction(var);
    }

    @Override
    public final void enterCompilationUnit(final SMTModelParser.CompilationUnitContext ctx) {

        model.setSMTModelAsString(AntlrUtil.getFormattedText(ctx));
    }

    @Override
    public AntlrParseResult getParseResult() {
        return model;
    }
}
