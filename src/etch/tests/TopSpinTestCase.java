package src.etch.tests;

import java.util.Set;

public abstract class TopSpinTestCase {

	protected String filename;

	private TestOutcome expectedOutcome;
	protected TestOutcome actualOutcome;
	
	public TopSpinTestCase(String filename, TestOutcome outcome) {
		this.filename = filename;
		this.expectedOutcome = outcome;
	}

	public boolean isPass() {
		return expectedOutcome.matches(actualOutcome);
	}

	public abstract void run();

	public static void displayResults(Set<TopSpinTestCase> passes, Set<TopSpinTestCase> fails) {

		System.out.println("PASSES");
		System.out.println("======");
		
		for(TopSpinTestCase testCase : passes) {
			System.out.println("  " + testCase.filename + " - expected and actual: " + testCase.expectedOutcome);
		}
		
		System.out.println("\nFAILS");
		System.out.println("=====");

		for(TopSpinTestCase testCase : fails) {
			System.out.println("  " + testCase.filename + " - expected: " + testCase.expectedOutcome + ", actual: " + testCase.actualOutcome);
		}
		
		System.out.println("Summary:");
		System.out.println("   " + passes.size() + " passes");
		System.out.println("   " + fails.size() + " fails");
	}
	
}
