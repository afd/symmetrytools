package src.symmextractor.testing;

import src.testing.TestOutcome;

public enum SymmExtractorFailTestOutcome implements SymmExtractorTestOutcome {

	BreaksRestrictions;		

	public boolean matches(TestOutcome actualOutcome) {

		return actualOutcome == BreaksRestrictions;

	}
	
}
