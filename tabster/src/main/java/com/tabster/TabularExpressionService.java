package com.tabster;

import java.util.ArrayList;

import com.tabster.expression.AntlrParser;
import com.tabster.expression.ExpressionParserFactory;
import com.tabster.expression.ITabularExpressionParser;
import com.tabster.expression.SMTLIBDescriptionBuilder;
import com.tabster.smtmodel.SMTModel;

/**
 * Service class for parsing/solving tabular expressions.
 *
 * @author Muntazir Fadhel
 */
public final class TabularExpressionService {

    /**
     * Generates a SMT-LIB v2 compliant script for checking the satisfiability
     * and for getting the model of a given tabular expression.
     *
     * @param tabularExpression
     *            String containing a tabular expression.
     * @return String representing the SMT-LIB script input to a SMT solver.
     * @throws Exception
     *             When generating the script encounters an error.
     */
    public static String extractSMTLibSolverScript(final String tabularExpression) throws Exception {
        final FactoryProducer factoryProducer = new FactoryProducer();
        final AbstractFactory abstractFactory = factoryProducer.getFactory(ExpressionParserFactory.PARSER_FACTORY_KEY);
        final ITabularExpressionParser parser = abstractFactory.getExpressionParsingTool();
        final String sMTsmtLibSolverScript = ((SMTLIBDescriptionBuilder) parser
                .extractParseResult(tabularExpression)).getSMTLIBDescription();
        return sMTsmtLibSolverScript;
    }

    /**
     * Extracts the SMT-LIB functions from a String representing SMT-LIB Model
     * Output.
     *
     * @param smtLibModelOutput
     *            String containing SMT-LIB model output
     * @return List of SMT Functions representing the model functions
     * @throws Exception
     *             When an error is encountered duing the extraction process.
     */
    public static ArrayList<SMTFunction> extractModelFunctions(final String smtLibModelOutput) throws Exception {
        final AntlrParser parser = new AntlrParser("SMTModel", "smtmodel",
                "com.tabster.smtmodel.TabsterSMTModelListener",
                "com.tabster.smtmodel.SMTModel");
        final SMTModel smtModel = (SMTModel) parser.extractParseResult(smtLibModelOutput);
        return smtModel.getFunctions();
    }

    /**
     * Utility class should not have a public/default constructor.
     */
    private TabularExpressionService() {
    }
}
