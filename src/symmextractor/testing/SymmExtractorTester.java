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

		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/mutex/", "mutex5.p", new SymmExtractorRunTestOutcome(true, 120, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/mutex/", "mutex10.p", new SymmExtractorRunTestOutcome(true, 3628800, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "3-3-2.p", new SymmExtractorRunTestOutcome(true, 144, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "3-3-3.p", new SymmExtractorRunTestOutcome(true, 1296, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "4-4-3.p", new SymmExtractorRunTestOutcome(true, 6912, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "4-4-4.p", new SymmExtractorRunTestOutcome(true, 82944, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "5-5-5-5.p", new SymmExtractorRunTestOutcome(true, 4976640000L, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "threetierdynamic.p", new SymmExtractorRunTestOutcome(true, 1296, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/threetiered/", "threetiersmall.p", new SymmExtractorRunTestOutcome(true, 72, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/ring/", "ring.p", new SymmExtractorRunTestOutcome(true, 3, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/peterson/", "peterson3.p", new SymmExtractorRunTestOutcome(true, 6, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/peterson/", "peterson6.p", new SymmExtractorRunTestOutcome(true, 720, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/peterson/", "peterson9.p", new SymmExtractorRunTestOutcome(true, 362880, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/peterson/", "peterson12.p", new SymmExtractorRunTestOutcome(true, 479001600, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/petersonnoatomic/", "3.p", new SymmExtractorRunTestOutcome(true, 6, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/petersonnoatomic/", "6.p", new SymmExtractorRunTestOutcome(true, 720, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/petersonnoatomic/", "9.p", new SymmExtractorRunTestOutcome(true, 362880, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/petersonnoatomic/", "12.p", new SymmExtractorRunTestOutcome(true, 479001600, false)));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "basic.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "email.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "loadbalancer.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "misc2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "potsmodel.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "priority.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "sharing.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "telephone.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failrunsdynamicchannel.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failchannelintypedef.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failactiveproctype.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failactiveproctype2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failrunsdynamicprocess.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failincrementpid.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "faildecrementpid.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "faildecrementpid2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failarithonpid.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failarithonpid2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failpidindexedarraywithwronglength.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/BadlyTyped/", "failpidindexedarraywithwronglength2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));

				
		missingFeatureTestCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/MissingFeatures/loadbalancer/", "loadbalancer.p", new SymmExtractorRunTestOutcome(true, 432, false)));
		missingFeatureTestCases.add(new SymmExtractorTestCase("TestModels/SymmExtractorTests/MissingFeatures/", "failrunsdynamicprocess.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		
		return testCases;
	}	

	
	public static void main(String args[]) {
		runTests();
		Tester.displayResults();
	}

}
