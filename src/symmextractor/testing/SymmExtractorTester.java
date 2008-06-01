package src.symmextractor.testing;

import java.util.HashSet;
import java.util.Set;

import src.testing.Tester;
import src.testing.TestCase;

public class SymmExtractorTester {

	public static void runTests() {
		System.out.println("SYMMEXTRACTOR TESTS");
		System.out.println("===================");
		Tester.runTests(getTestCases());
	}

	private static Set<TestCase> getTestCases() {

		Set<TestCase> testCases = new HashSet<TestCase>();
		Set<TestCase> missingFeatureTestCases = new HashSet<TestCase>();

		/*************/
		/* RUN TESTS */
		/*************/
		
		testCases.add(new SymmExtractorTestCase("mutex/", "mutex5.p", new SymmExtractorRunTestOutcome(true, 120, false)));
		testCases.add(new SymmExtractorTestCase("mutex/", "mutex10.p", new SymmExtractorRunTestOutcome(true, 3628800, false)));

		testCases.add(new SymmExtractorTestCase("threetiered/", "3-3-2.p", new SymmExtractorRunTestOutcome(true, 144, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "3-3-3.p", new SymmExtractorRunTestOutcome(true, 1296, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "4-4-3.p", new SymmExtractorRunTestOutcome(true, 6912, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "4-4-4.p", new SymmExtractorRunTestOutcome(true, 82944, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "5-5-5-5.p", new SymmExtractorRunTestOutcome(true, 4976640000L, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "threetierdynamic.p", new SymmExtractorRunTestOutcome(true, 1296, false)));
		testCases.add(new SymmExtractorTestCase("threetiered/", "threetiersmall.p", new SymmExtractorRunTestOutcome(true, 72, false)));
		testCases.add(new SymmExtractorTestCase("ring/", "ring.p", new SymmExtractorRunTestOutcome(true, 3, false)));

		testCases.add(new SymmExtractorTestCase("peterson/", "peterson3.p", new SymmExtractorRunTestOutcome(true, 6, false)));
		testCases.add(new SymmExtractorTestCase("peterson/", "peterson6.p", new SymmExtractorRunTestOutcome(true, 720, false)));
		testCases.add(new SymmExtractorTestCase("peterson/", "peterson9.p", new SymmExtractorRunTestOutcome(true, 362880, false)));
		testCases.add(new SymmExtractorTestCase("peterson/", "peterson12.p", new SymmExtractorRunTestOutcome(true, 479001600, false)));

		testCases.add(new SymmExtractorTestCase("petersonnoatomic/", "3.p", new SymmExtractorRunTestOutcome(true, 6, false)));
		testCases.add(new SymmExtractorTestCase("petersonnoatomic/", "6.p", new SymmExtractorRunTestOutcome(true, 720, false)));
		testCases.add(new SymmExtractorTestCase("petersonnoatomic/", "9.p", new SymmExtractorRunTestOutcome(true, 362880, false)));
		testCases.add(new SymmExtractorTestCase("petersonnoatomic/", "12.p", new SymmExtractorRunTestOutcome(true, 479001600, false)));

		
		/**************/
		/* FAIL TESTS */
		/**************/

		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "basic.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "email.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "loadbalancer.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "misc2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "potsmodel.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "priority.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "sharing.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("BadlyTyped/", "telephone.p", SymmExtractorFailTestOutcome.BreaksRestrictions));

		
		
		missingFeatureTestCases.add(new SymmExtractorTestCase("loadbalancer/", "loadbalancer.p", new SymmExtractorRunTestOutcome(true, 432, false)));

		
		return testCases;
	}	

	
	public static void main(String args[]) {
		runTests();
		Tester.displayResults();
	}

}
