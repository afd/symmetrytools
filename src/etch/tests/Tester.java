package src.etch.tests;

import java.util.HashSet;
import java.util.Set;

import src.utilities.Config;

public class Tester {

	public static int runTests(Set<TopSpinTestCase> testCases) {

		Config.TESTING_IN_PROGRESS = true;
		
		Set<TopSpinTestCase> passes = new HashSet<TopSpinTestCase>();
		Set<TopSpinTestCase> fails = new HashSet<TopSpinTestCase>();
		
		for(TopSpinTestCase testCase : testCases) {
			testCase.run();
			if(testCase.isPass()) {
				passes.add(testCase);
			} else {
				fails.add(testCase);
			}
		}
		
		TopSpinTestCase.displayResults(passes, fails);

		if(fails.size()>0) {
			return 1;
		}
	
		return 0;
	}

}
