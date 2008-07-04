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

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), 40));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), 40));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), "-DNUM_THREADS=4", 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), "-DNUM_THREADS=6", 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), "-DNUM_THREADS=3", 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), "-DNUM_THREADS=2", 40));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), "-DNUM_THREADS=4", 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), "-DNUM_THREADS=6", 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), "-DNUM_THREADS=3", 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), "-DNUM_THREADS=2", 40));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=2"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=3"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=4"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=5"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=2"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=3"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=4"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=9"));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 251, 752)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 1177, 4706)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5148, 25737)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 21752, 130508)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 17717, 124014), 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/vector_flatten/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 1177, 4706)));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 494, 1481)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 3106, 12422)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 17321, 86602)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 89850, 539096), 25000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 142669, 998678), 100));
						
		return testCases;
	}
	
	public static void main(String args[]) {
		runTests();
		Tester.displayResults();
	}
	
}

