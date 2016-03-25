package com.tabster.expression;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.tabster.SMTFunction;

/**
 * Processes expressions to build a SMT-Lib Standard v2.5 description, see
 * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.5-r2015-06-28.pdf for
 * more details...
 *
 * @author Muntazir Fadhel
 */
public class SMTLIBDescription {

	ArrayList<SMTFunction> expressionInputs;
	private String plainTabularExpression;
	private boolean getModel;
	private boolean checkSat;
	public SMTLIBDescription(ArrayList<SMTFunction> expressionInputs, String originalTabularExpression, boolean checkSat, boolean getModel) {
		this.expressionInputs = expressionInputs;
		this.setPlainTabularExpression(originalTabularExpression);
		declareTerms(this.expressionInputs);
		this.smtLIBDescription += " (assert ";
		this.checkSat = checkSat;
		this.getModel = getModel;
	}
	
	public String getEndingString() {
		
		 String SMT_LIB_DESC_END = ") ";

		if (checkSat) {
			SMT_LIB_DESC_END += "(check-sat) ";
		}
		if (getModel) {
			SMT_LIB_DESC_END += "(get-model) ";
		}
		SMT_LIB_DESC_END += "(exit)";
		
		return SMT_LIB_DESC_END;
	}
    /**
     * Maps common expression operators to their equivalent SMT LIB String
     * representation.
     */
    static final Map<String, String> SMT_LIB_OPERATOR_MAP = new HashMap<String, String>();
    static {
        SMT_LIB_OPERATOR_MAP.put("+", "+");
        SMT_LIB_OPERATOR_MAP.put("-", "-");
        SMT_LIB_OPERATOR_MAP.put("=", "=");
        SMT_LIB_OPERATOR_MAP.put("&", "and");
        SMT_LIB_OPERATOR_MAP.put("|", "or");
        SMT_LIB_OPERATOR_MAP.put("!", "not");
        SMT_LIB_OPERATOR_MAP.put("~", "not");
        SMT_LIB_OPERATOR_MAP.put("||", "or");
        SMT_LIB_OPERATOR_MAP.put("&&", "and");
        SMT_LIB_OPERATOR_MAP.put("*", "*");
        SMT_LIB_OPERATOR_MAP.put("/", "/");
        SMT_LIB_OPERATOR_MAP.put("==", "=");
        SMT_LIB_OPERATOR_MAP.put(">", ">");
        SMT_LIB_OPERATOR_MAP.put("<", "<");
        SMT_LIB_OPERATOR_MAP.put("<=", "<=");
        SMT_LIB_OPERATOR_MAP.put(">=", ">=");
        SMT_LIB_OPERATOR_MAP.put("%", "mod");
        SMT_LIB_OPERATOR_MAP.put("!=", "!=");
        SMT_LIB_OPERATOR_MAP.put("∀", "forall");
        SMT_LIB_OPERATOR_MAP.put("∃", "exists");
        SMT_LIB_OPERATOR_MAP.put("∧", "and");
        SMT_LIB_OPERATOR_MAP.put("∨", "or");
    }

   
    private static final String SMT_LIB_DESC_BEGIN = "(set-logic AUFLIRA) (set-option :produce-models true) ";

    private String smtLIBDescription = SMT_LIB_DESC_BEGIN;

    public String getSMTLIBDescription() {
        return smtLIBDescription + getEndingString();
    }
    
    @Override
    public String toString() {
    	return getSMTLIBDescription();
    }

    public void registerExpressionEnd() {
        smtLIBDescription += ") ";
    }

    public void registerNewTerm(String term) {
        smtLIBDescription += term + " ";
    }

    /**
     * Registers the start of a new sub expression within the tabular
     * expression.
     *
     * @param expressionOperatorStr
     *            operator used in the sub expression.
     */
    public void registerExpressionStart(final String expressionOperatorStr) {

        if (SMT_LIB_OPERATOR_MAP.containsKey(expressionOperatorStr)) {
            smtLIBDescription += "(" + SMT_LIB_OPERATOR_MAP.get(expressionOperatorStr) + " ";
        } else {
            throw new IllegalArgumentException(expressionOperatorStr
                    + " could not be processed in the tabular expression!");
        }
    }

    /**
     * @param variableName
     *            name of the new term to declare
     */
    public void declareTerms(ArrayList<SMTFunction> inputs) {
    	for (SMTFunction input : inputs) {
    		smtLIBDescription += "(declare-fun " + input.getVarName() + " () " + input.getType().getValue() + ") ";   
    	}
    }

	/**
	 * @return the plainTabularExpression
	 */
	public String getPlainTabularExpression() {
		return plainTabularExpression;
	}

	/**
	 * @param plainTabularExpression the plainTabularExpression to set
	 */
	public void setPlainTabularExpression(String plainTabularExpression) {
		this.plainTabularExpression = plainTabularExpression;
	}

	public void registerPredicateExpressionStart(String quantifierSymbol,
			String variable) throws Exception {
		String type = null;
		for (SMTFunction possibleMatchingInput : expressionInputs) {
			if (possibleMatchingInput.getVarName().equals(variable)) {
				type = possibleMatchingInput.getType().getValue();
			}
		}
		if (type == null) {
			throw new Exception("Could not translate predicate expression!");
		}
		registerExpressionStart(quantifierSymbol);
		smtLIBDescription += "((" + variable + " " + type + ")) "; 
		
	}
}
