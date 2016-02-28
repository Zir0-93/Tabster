package com.tabster.expression;

import java.lang.reflect.Method;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeListener;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import com.tabster.AntlrParseResult;
import com.tabster.ITabsterANTLRParseTreeListener;

/**
 * Uses ANTLR to parse any data using specified project relative locations of
 * ANTLR parser files.
 *
 * @author Muntazir Fadhel
 */
public class AntlrParser implements ITabularExpressionParser {

    /**
     * The package in which the antlr source files are located in.
     */
    private final String antlrClassesPackageLocation;
    /**
     * grammar name (eg Java, C++).
     */
    private final String grammarName;

    private final String parseTreeListenerObjectLocation;

    private final String parseResultObjectLocation;

    /**
     * @param parserGrammarName
     *            name of the antlr grammer file excluding the '.g4' extension
     * @param parserAntlrClassesPackageLocation
     *            type of parseResult Object to be populated by the anltr parser
     * @param parseTreeListenerObjectLocation
     *            the package location of the ParseTree Listener to use for the
     *            parser
     * @param parseResultObjectLocation
     *            the full name of the Object that will hold the output of the
     *            parse operation data that needs to be parsed
     * @throws Exception
     *             Exception
     */
    public AntlrParser(final String parserGrammarName, final String parserAntlrClassesPackageLocation,
            final String parseTreeListenerObjectLocation, final String parseResultObjectLocation) throws Exception {

        grammarName = parserGrammarName;
        antlrClassesPackageLocation = parserAntlrClassesPackageLocation;
        this.parseTreeListenerObjectLocation = parseTreeListenerObjectLocation;
        this.parseResultObjectLocation = parseResultObjectLocation;
    }


    @Override
    public <T extends AntlrParseResult> Object extractParseResult(final String rawString)
            throws Exception {

        Class
        .forName(parseResultObjectLocation)
        .getConstructor().newInstance();
        final Lexer lexer = (Lexer) Class.forName(antlrClassesPackageLocation + "." + grammarName + "Lexer")
                .getConstructor(CharStream.class)
                .newInstance(new ANTLRInputStream(rawString));
        final CommonTokenStream tokens = new CommonTokenStream(lexer);
        final Class<?> cls = Class.forName(antlrClassesPackageLocation + "." + grammarName + "Parser");
        final Object parser = cls.getConstructor(TokenStream.class).newInstance(tokens);
        final Method method = cls.getDeclaredMethod("compilationUnit");
        final ParseTree tree = (ParseTree) method.invoke(parser);
        final ParseTreeWalker walker = new ParseTreeWalker();
        final ITabsterANTLRParseTreeListener listener = (ITabsterANTLRParseTreeListener) Class
                .forName(parseTreeListenerObjectLocation)
                .getConstructor().newInstance();
        walker.walk((ParseTreeListener) listener, tree);
        return listener.getParseResult();
    }
}
