package src.testing;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import src.utilities.Config;

public class Tester {

	static Set<TestCase> passes = new HashSet<TestCase>();
	static Set<TestCase> fails = new HashSet<TestCase>();

	public static void runTests(List<TestCase> testCases) {

		Config.TESTING_IN_PROGRESS = true;
				
		for(TestCase testCase : testCases) {

			Config.resetConfiguration();
			testCase.run();

			if(testCase.isPass()) {
				passes.add(testCase);
			} else {
				fails.add(testCase);
			}
			
			testCase.displayResult();
		}
		
		System.out.println("\n");
	}

	public static void displayResults() {
		System.out.println("Summary:");
		System.out.println("   " + passes.size() + " passes");
		System.out.println("   " + fails.size() + " fails");
		
		
		if(fails.isEmpty()) {
			System.out.println("\n\nAcceptance tests passed - you may commit your changes!");
		} else {
			System.out.println("\n\nAcceptance tests failed - fix all problems before committing.");
		}
			
	}

}
