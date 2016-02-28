package com.tabster.expression;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import com.tabster.AntlrParseResult;

/**
 * Processes expressions to build a SMT-Lib Standard v2.5 description, see
 * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.5-r2015-06-28.pdf for
 * more details...
 *
 * @author Muntazir Fadhel
 */
public class SMTLIBDescriptionBuilder implements AntlrParseResult {

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
    }

    /**
     * Keeps track of all the variables being used in the SMTLib Description.
     */
    private final ArrayList<String> variables = new ArrayList<String>();

    private static final String SMT_LIB_DESC_END = ") (check-sat) (get-model) (exit)";

    private static final String SMT_LIB_DESC_BEGIN = "(assert ";

    private String smtLIBDescription = SMT_LIB_DESC_BEGIN;

    public String getSMTLIBDescription() {
        return smtLIBDescription + SMT_LIB_DESC_END;
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
    public void declareNewTerm(final String variableName) {
        if (!variables.contains(variableName)) {
            smtLIBDescription = "(declare-fun " + variableName + " () Int) " + smtLIBDescription;
            variables.add(variableName);
        }
    }
}
