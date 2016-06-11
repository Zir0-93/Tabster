package com.tabster;

import java.util.ArrayList;
import java.util.List;

public class PropertyVerificationResult {

    private boolean           satisfied;
    private List<SMTFunction> counterExamples;

    public PropertyVerificationResult(boolean satisfied, List<SMTFunction> counterExamples) {

        init(satisfied, counterExamples);
    }

    public PropertyVerificationResult(boolean satisfied) {

        init(satisfied, new ArrayList<SMTFunction>());
    }

    private void init(boolean satisfied, List<SMTFunction> counterExamples) {

        this.satisfied = satisfied;
        this.counterExamples = counterExamples;
    }

    public boolean satisfied() {
        return this.satisfied;
    }

    public List<SMTFunction> counterExamples() {
        return this.counterExamples;
    }
}
