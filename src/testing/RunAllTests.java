package src.testing;

import src.etch.testing.EtchTester;
import src.symmextractor.testing.SymmExtractorTester;

public class RunAllTests {

	public static void main(String[] args) {
		EtchTester.runTests();
		SymmExtractorTester.runTests();
		Tester.displayResults();
	}
	
}
