package src.testing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import src.translator.ModelType;

public class GRIPTester {

	public static void runTests() {
		System.out.println("GRIP TESTS");
		System.out.println("==========");
		Tester.runTests(getTestCases());
	}
	
	public static void main(String args[]) throws IOException {
		runTests();
		Tester.displayResults();
	}

	private static List<TestCase> getTestCases() {
		List<TestCase> testCases = new ArrayList<TestCase>();

		runUnitTests();
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/mutual3.nm", new GRIPPassTestOutcome(ModelType.nondeterministic, 1894, 470, 1541, 1460)));

		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader20.nm", new GRIPPassTestOutcome(ModelType.nondeterministic, 1774, 231, 480, 460)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader30.nm", new GRIPPassTestOutcome(ModelType.nondeterministic, 2562, 496, 1020, 990)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader20.nm", true, false, new GRIPPassTestOutcome(ModelType.nondeterministic, 1354, 231, 480, 460)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader30.nm", true, false, new GRIPPassTestOutcome(ModelType.nondeterministic, 1942, 496, 1020, 990)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader20.nm", false, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 854, 231, 480, 460)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader30.nm", false, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 1170, 496, 1020, 990)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader20.nm", true, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 433, 231, 480, 460)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/leader30.nm", true, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 549, 496, 1020, 990)));

		testCases.add(new GRIPTestCase("TestModels/GRIPTests/byzantine8.forgrip.nm", true, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 167372, 298993, 1476250, 1440348)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/byzantine8.forgrip.nm", new GRIPPassTestOutcome(ModelType.nondeterministic, 175046, 298993, 1476250, 1440348)));

		testCases.add(new GRIPTestCase("TestModels/GRIPTests/consensus8.forgrip.nm", new GRIPPassTestOutcome(ModelType.nondeterministic, 24027, 46482, 200408, 172160)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/consensus8.forgrip.nm", true, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 15598, 46482, 200408, 172160)));

		testCases.add(new GRIPTestCase("TestModels/GRIPTests/rabin5.forgrip.nm", true, true, new GRIPPassTestOutcome(ModelType.nondeterministic, 123512, 87312, 1788808, 410176)));

		testCases.add(new GRIPTestCase("TestModels/GRIPTests/fgf4.forgrip.sm", true, true, new GRIPPassTestOutcome(ModelType.stochastic, 262871, 12397, 156181, -1)));
		
		testCases.add(new GRIPTestCase("TestModels/GRIPTests/fgf4.forgrip.sm", new GRIPPassTestOutcome(ModelType.stochastic, 399078, 12397, 156181, -1)));
		
		return testCases;

	}

	private static void runUnitTests() {

	}

}
