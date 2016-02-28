package com.tabster;

import com.tabster.expression.ITabularExpressionParser;


/**
 * @author Muntazir Fadhel
 */
public abstract class AbstractFactory {

    /**
     * @return A suitable Tabular Expression Parser
     * @throws Exception
     *             when factory cannot handle/process input.
     */
    public abstract ITabularExpressionParser getExpressionParsingTool() throws Exception;

}
