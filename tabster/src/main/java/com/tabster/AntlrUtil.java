package com.tabster;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

/**
 * Utility class for Antlr.
 *
 * @author Muntazir Fadhel
 */
public final class AntlrUtil {

    /**
     * @param context
     *            parse tree context whose String we need to get the formatted
     *            text off.
     * @return formatted text as a string
     */
    public static String getFormattedText(final ParserRuleContext context) {

        try {
            if ((context.start == null) || (context.stop == null) || (context.start.getStartIndex() < 0)
                    || (context.stop.getStopIndex() < 0)) {
                return context.getText(); // fallback
            }

            return context.start.getInputStream().getText(
                    Interval.of(context.start.getStartIndex(), context.stop.getStopIndex()));
        } catch (final StringIndexOutOfBoundsException e) {
            e.printStackTrace();
            return "";
        }
    }

    /**
     *
     */
    private AntlrUtil() {

    }
}
