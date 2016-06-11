package com.tabster;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.BailErrorStrategy;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.apache.commons.io.IOUtils;

import com.tabster.expression.SMTLIBDescription;
import com.tabster.expression.PredicateExpressionListener;
import com.tabster.smtmodel.SMTModel;
import com.tabster.smtmodel.TabsterSMTModelListener;

import expression.PredicateExpressionLexer;
import expression.PredicateExpressionParser;
import com.tabster.expression.PredicateExpression;
import smtmodel.SMTModelLexer;
import smtmodel.SMTModelParser;

/**
 * Service class for parsing/solving tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public final class TabularExpression {

    private ArrayList<String>      tabularExpression;
    private ArrayList<SMTFunction> expressionVars;

    public TabularExpression(ArrayList<String> tabularExpression, ArrayList<SMTFunction> expressionVars) {
        this.tabularExpression = tabularExpression;
        this.expressionVars = expressionVars;
    }

    /**
     * The given tabular expression is complete when the returned model
     * is not satisfiable, otherwise the expression is incomplete. If the 
     * expression is incomplete, the values of the SMTFunctions within the
     * model will include counter examples.
     */
    public PropertyVerificationResult checkCompleteness() throws Exception {

        // to check for completion, check if the following expression is satisfiable:
        String completionCheckExpression = "";
        for (String predExpr : tabularExpression) {
            completionCheckExpression += "!(" + predExpr + ") ∧ ";
        }
        // remove the last LOGICAL AND
        completionCheckExpression = completionCheckExpression.substring(0, completionCheckExpression.length() - 2);
        SMTModel model = new SMTModel(new PredicateExpression(completionCheckExpression, this.expressionVars).solve(), this.expressionVars);
        if (model.sat()) {
            return new PropertyVerificationResult(false, model.functions());
        } else {
            return new PropertyVerificationResult(true);
        }
    }

    /**
     * If the returned model is satisfiable, the given expression are
     * not disjoint. In this case the returned SMTFunctions will show counter
     * examples. If the model is not satisfiable, then the given tabular
     * expressions is disjoint.
     */
    public PropertyVerificationResult checkDisjointness() throws Exception {
        // The basic strategy to determine disjointness is to ensure that no two condition rows
        // in the table when AND'ed together are satisifiable.
        for (int i = tabularExpression.size() - 1; i > 0; i--) {
            for (int j = i - 1; j >= 0; j--) {
                String checkExpression = tabularExpression.get(i) + " ∧ " + tabularExpression.get(j);
                // if the problem is satisfiable, that is, the returned input variables have values, the tabular
                // expression is not complete
                 SMTModel model = new SMTModel(new PredicateExpression(checkExpression, this.expressionVars).solve(), this.expressionVars);
                if (model.sat()) {
                    return new PropertyVerificationResult(false, model.functions());
                }
            }
        }
        // expressions are disjoint!
        return new PropertyVerificationResult(true);
    }
}
