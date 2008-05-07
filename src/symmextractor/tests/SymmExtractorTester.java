package src.symmextractor.tests;

import java.util.HashSet;
import java.util.Set;

import src.etch.tests.Tester;
import src.etch.tests.TopSpinTestCase;

public class SymmExtractorTester {


	private static Set<TopSpinTestCase> getTestCases() {

		Set<TopSpinTestCase> testCases = new HashSet<TopSpinTestCase>();

		testCases.add(new SymmExtractorTestCase("SymmetryReductionTests/mutex/mutex5.p", new SymmExtractorTestOutcome(true, 120, false)));

		return testCases;
	}	

	
	public static void main(String args[]) {
		System.exit(Tester.runTests(getTestCases()));
	}

}
