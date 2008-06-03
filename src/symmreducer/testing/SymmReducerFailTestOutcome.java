package src.symmreducer.testing;

import src.testing.TestOutcome;

public enum SymmReducerFailTestOutcome implements TestOutcome {
	VerificationIOError, VerificationInterrupted, GCCCompilationIOError, GCCCompilationInterrupted, GCCCompilationFailure, VerificationFailure, ErrorParsingVerificationResult;

	public boolean matches(TestOutcome actualOutcome) {

		return this == actualOutcome;

	}

}
