package com.tabster;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

public class FormattedParserRuleContextString {

    private ParserRuleContext context;

    public FormattedParserRuleContextString(final ParserRuleContext context) {

        this.context = context;
    }

    public String formattedString() {
        try {
            if ((this.context.start == null) || (this.context.stop == null) || (this.context.start.getStartIndex() < 0)
                || (this.context.stop.getStopIndex() < 0)) {
                return this.context.getText(); // fallback
            }

            return this.context.start.getInputStream().getText(Interval.of(this.context.start.getStartIndex(),
                                                                           this.context.stop.getStopIndex()));
        } catch (final StringIndexOutOfBoundsException e) {
            e.printStackTrace();
            return "";
        }
    }
}
