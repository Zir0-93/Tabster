package com.tabster.expression;

import com.tabster.AntlrParseResult;


/**
 * All Tabular Expression parsers should be able to parse a tabular expression
 * and return the SMT-LIB Description of the tabular expression.
 *
 * @author Muntazir Fadhel
 */
public interface ITabularExpressionParser {

    /**
     * @param tabularExpressionString
     *            The String containing the tabular expression to be parsed
     * @param <T>
     *            Generic
     * @return A SMT-LIB Description of the tabular expression
     * @throws Exception
     *             When there is an error during the parsing operation
     */
    <T extends AntlrParseResult> Object extractParseResult(String tabularExpressionString) throws Exception;
}
