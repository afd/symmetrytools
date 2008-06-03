package src.symmreducer.testing;

import java.util.HashSet;
import java.util.Set;

import src.symmextractor.testing.SymmExtractorRunTestOutcome;
import src.testing.TestCase;
import src.testing.Tester;

public class SymmReducerTester {

	public static void runTests() {
		System.out.println("SYMMREDUCER TESTS");
		System.out.println("=================");
		Tester.runTests(getTestCases());
	}

	private static Set<TestCase> getTestCases() {

		Set<TestCase> testCases = new HashSet<TestCase>();
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/enumerate_basic/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/enumerate_basic_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/enumerate_stabchain/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/enumerate_stabchain_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_stabchain/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_stabchain_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic/", "mutex10.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 3628800, false), 22, 167)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex10.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 3628800, false), 22, 167)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic/", "mutex15.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1307674368000L, false), 32, 362)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex15.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1307674368000L, false), 32, 362)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic/", "mutex20.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2432902008176640000L, false), 42, 632)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex20.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2432902008176640000L, false), 42, 632)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_swaps/", "3s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1296, false), 50396, 407839), 100000));

		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/enumerate_basic/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/enumerate_basic_swaps/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/enumerate_stabchain/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/enumerate_stabchain_swaps/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_noswaps/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_swaps/", "2s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 72, false), 2656, 14879)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_noswaps/", "2s4cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1152, false), 5021, 35419)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_swaps/", "2s4cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1152, false), 5021, 35419)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/threetiered/fast_noswaps/", "3s3cs.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1296, false), 631, 3883), 30));

		return testCases;
	}
	
	public static void main(String args[]) {
		runTests();
		Tester.displayResults();
	}
	
}

