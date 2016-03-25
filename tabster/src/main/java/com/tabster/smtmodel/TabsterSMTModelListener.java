package com.tabster.smtmodel;

import smtmodel.SMTModelBaseListener;
import smtmodel.SMTModelParser;

import com.tabster.AntlrUtil;
import com.tabster.SMTFunction;
import com.tabster.SMTFunction.FunctionType;

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
	private String currentVarName;
	private boolean sat;

	/**
	 * Public constructor.
	 */
	public TabsterSMTModelListener(SMTModel smtModel) {
		model = smtModel;
	}

	@Override
	public final void exitFunctionDeclaration(final SMTModelParser.FunctionDeclarationContext ctx) {

		String discoveredVarType = ctx.varType().getText();
		String discoveredVarValue;
		if (ctx.varValue().divisionStatement() != null) {
			if (discoveredVarType.equals(FunctionType.INT.getValue())) {
				discoveredVarValue = String.valueOf((int)(Float.valueOf(ctx.varValue().divisionStatement().FloatingPointLiteral(0).toString()) 
						/ Float.valueOf(ctx.varValue().divisionStatement().FloatingPointLiteral(1).toString())));
			} else {
				discoveredVarValue = String.valueOf((Float.valueOf(ctx.varValue().divisionStatement().FloatingPointLiteral(0).toString()) 
						/ Float.valueOf(ctx.varValue().divisionStatement().FloatingPointLiteral(1).toString())));
			}
		} else {
			discoveredVarValue = ctx.varValue().getText();
		}
		for (SMTFunction var : model.getFunctions()) {
			if (var.getVarName().equals(currentVarName)
					&& var.getType().getValue().equals(discoveredVarType)) {
				var.setValue(discoveredVarValue);
			}
		}    	
	}
	
	@Override
	public final void enterSatResult(final SMTModelParser.SatResultContext ctx) {

		if (ctx.getText().equals("unsat")) {
			model.setSat(false);
		} else {
			model.setSat(true);
		}
	}

	@Override
	public final void enterVarName(final SMTModelParser.VarNameContext ctx) {

		currentVarName = ctx.Identifier().getText();
	}

    @Override
    public final void enterCompilationUnit(final SMTModelParser.CompilationUnitContext ctx) {

        model.setSMTModelAsString(AntlrUtil.getFormattedText(ctx));
    }

    public SMTModel getParseResult() {
        return model;
    }
}
