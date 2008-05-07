package src.symmextractor.tests;

import java.io.IOException;

import src.etch.tests.TopSpinTestCase;
import src.symmextractor.SymmExtractor;

public class SymmExtractorTestCase extends TopSpinTestCase {

	public SymmExtractorTestCase(String filename, SymmExtractorTestOutcome expectedOutcome) {
		
		super(filename, expectedOutcome);
		
	}

	@Override
	public void run() {

		try {
		
			SymmExtractor extractor = new SymmExtractor(filename);

			if(!extractor.isWellTyped(true)) {
				actualOutcome = new SymmExtractorTestOutcome(false, 0, false);
			} else {
				extractor.extract();
				actualOutcome = new SymmExtractorTestOutcome(true, extractor.getSizeOfGroup(), extractor.requiredCosetSearch());
			}
			
		} catch(IOException e) {
			
			// Mark the test as a fail.
			
		}
		
	}
}
