package com.tabster.expression;

import com.tabster.AbstractFactory;

/**
 * Factory to retrieve appropriate parsing tool for our projects.
 *
 * @author Muntazir Fadhel
 */
public class ExpressionParserFactory extends AbstractFactory {

    public static final String PARSER_FACTORY_KEY = "parser";

    @Override
    public ITabularExpressionParser getExpressionParsingTool() throws Exception {

        return new AntlrParser("TabularExpression", "expression",
                "com.tabster.expression.TabsterTabularExpressionListener",
                "com.tabster.expression.SMTLIBDescriptionBuilder");
    }
}
