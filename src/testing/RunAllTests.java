package src.testing;

import src.etch.testing.EtchTester;
import src.symmextractor.testing.SymmExtractorTester;
import src.symmreducer.testing.SymmReducerTester;

public class RunAllTests {

	public static void main(String[] args) {
		EtchTester.runTests();
		SymmExtractorTester.runTests();
		SymmReducerTester.runTests();
		Tester.displayResults();
	}
	
}
