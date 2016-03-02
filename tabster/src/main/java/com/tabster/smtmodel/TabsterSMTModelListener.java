package com.tabster.smtmodel;

import smtmodel.SMTModelBaseListener;
import smtmodel.SMTModelParser;

import com.tabster.AntlrUtil;
import com.tabster.SMTFunction;

/**
 * Once the parsing has done it�s job we�ll get ANTLR to walk the grammar and
 * attach a listener � the listener is notified when any one of our parsing
 * rules is triggered. We can use these listeners to build an appropriate
 * SMT-LIB Description of the given tabular expression in order to pass to any
 * SMT-LIB v2 compliant SMT solver.
 *
 * @author Muntazir Fadhel
 */
public class TabsterSMTModelListener extends SMTModelBaseListener {

    private final SMTModel model;

    /**
     * Public constructor.
     */
    public TabsterSMTModelListener(SMTModel smtModel) {
        model = smtModel;
    }

    @Override
    public final void enterFunctionDeclaration(final SMTModelParser.FunctionDeclarationContext ctx) {

    	String discoveredVarName = ctx.varName().getText();
    	String discoveredVarType = ctx.varType().getText();
    	String discoveredVarValue = ctx.varValue().getText();
    	
    	for (SMTFunction var : model.getFunctions()) {
    		if (var.getVarName().equals(discoveredVarName)
    				&& var.getType().getValue().equals(discoveredVarType)) {
    			var.setValue(discoveredVarValue);
    		}
    	}
    }

    @Override
    public final void enterCompilationUnit(final SMTModelParser.CompilationUnitContext ctx) {

        model.setSMTModelAsString(AntlrUtil.getFormattedText(ctx));
    }

    public SMTModel getParseResult() {
        return model;
    }
}
