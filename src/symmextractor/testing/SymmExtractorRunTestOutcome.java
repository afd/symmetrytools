package src.symmextractor.testing;

import src.testing.TestOutcome;

public class SymmExtractorRunTestOutcome implements SymmExtractorTestOutcome {

	private boolean wellTyped;
	
	private long groupSize;
	
	private boolean requiredCosetSearch;
	
	public SymmExtractorRunTestOutcome(boolean wellTyped, long groupSize, boolean requiredCosetSearch) {
		this.wellTyped = wellTyped;
		this.groupSize = groupSize;
		this.requiredCosetSearch = requiredCosetSearch;
	}

	public SymmExtractorRunTestOutcome(SymmExtractorRunTestOutcome symmExtractorOutcome) {
		this.wellTyped = symmExtractorOutcome.wellTyped;
		this.groupSize = symmExtractorOutcome.groupSize;
		this.requiredCosetSearch = symmExtractorOutcome.requiredCosetSearch;
	}

	public boolean matches(TestOutcome actualOutcome) {
		return (actualOutcome instanceof SymmExtractorRunTestOutcome) &&
		    (wellTyped == ((SymmExtractorRunTestOutcome)actualOutcome).wellTyped) &&
			(groupSize == ((SymmExtractorRunTestOutcome)actualOutcome).groupSize) &&
			(requiredCosetSearch == ((SymmExtractorRunTestOutcome)actualOutcome).requiredCosetSearch);
	}
	
	public String toString() {
		String result = "(";
		if(!wellTyped) {
			result += "not ";
		}
		result += "well typed, group size = " + groupSize + ", coset search: " + (requiredCosetSearch ? "yes" : "no") + ")";
		
		return result;
	}

}
