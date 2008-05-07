package src.symmextractor.tests;

import src.etch.tests.TestOutcome;

public class SymmExtractorTestOutcome implements TestOutcome {

	private boolean wellTyped;
	
	private int groupSize;
	
	private boolean requiredCosetSearch;
	
	public SymmExtractorTestOutcome(boolean wellTyped, int groupSize, boolean requiredCosetSearch) {
		this.wellTyped = wellTyped;
		this.groupSize = groupSize;
		this.requiredCosetSearch = requiredCosetSearch;
	}

	public boolean matches(TestOutcome actualOutcome) {
		return (actualOutcome instanceof SymmExtractorTestOutcome) &&
		    (wellTyped == ((SymmExtractorTestOutcome)actualOutcome).wellTyped) &&
			(groupSize == ((SymmExtractorTestOutcome)actualOutcome).groupSize) &&
			(requiredCosetSearch == ((SymmExtractorTestOutcome)actualOutcome).requiredCosetSearch);
	}

}
