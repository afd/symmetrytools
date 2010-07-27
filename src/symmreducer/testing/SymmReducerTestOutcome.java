package src.symmreducer.testing;

import src.symmextractor.testing.SymmExtractorRunTestOutcome;
import src.testing.TestOutcome;

public class SymmReducerTestOutcome extends SymmExtractorRunTestOutcome {

	private int numberOfStates;
	private int numberOfTransitions;
	
	public SymmReducerTestOutcome(SymmExtractorRunTestOutcome symmExtractorOutcome, int numberOfStates, int numberOfTransitions) {
		super(symmExtractorOutcome);
		this.numberOfStates = numberOfStates;
		this.numberOfTransitions = numberOfTransitions;
	}

	public boolean matches(TestOutcome actualOutcome) {
						
		return actualOutcome instanceof SymmReducerTestOutcome &&
			super.matches(actualOutcome) && 
			((SymmReducerTestOutcome)actualOutcome).numberOfStates==numberOfStates &&
			((SymmReducerTestOutcome)actualOutcome).numberOfTransitions==numberOfTransitions;
	}

	public String toString()
	{
		return "(" + super.toString() + ", " + "no. states: " + numberOfStates + ", no. transitions: " + numberOfTransitions + ")";
		
		
	}
	
}
