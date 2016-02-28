package com.tabster;

/**
 * Specifies the contract Tabster custom ANTLR tree listener adhere to.
 *
 * @author Muntazir Fadhel
 */
public interface ITabsterANTLRParseTreeListener {

    /**
     * Returns the result of the ANTLR parse operation.
     *
     * @return result of the parse operation
     */
    AntlrParseResult getParseResult();
}
