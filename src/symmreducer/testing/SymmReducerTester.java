package src.symmreducer.testing;

import java.util.ArrayList;
import java.util.List;

import src.symmextractor.testing.SymmExtractorFailTestOutcome;
import src.symmextractor.testing.SymmExtractorRunTestOutcome;
import src.testing.TestCase;
import src.testing.Tester;

public class SymmReducerTester {

	public static void runTests() {
		System.out.println("SYMMREDUCER TESTS");
		System.out.println("=================");
		Tester.runTests(getTestCases());
	}

	private static List<TestCase> getTestCases() {

		List<TestCase> testCases = new ArrayList<TestCase>();
		
	
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

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 251, 752)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 1177, 4706)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5148, 25737)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 21752, 130508)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/flatten/", "peterson7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 17717, 124014), 100));
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 494, 1481)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 3106, 12422)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 17321, 86602)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 89850, 539096), 25000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/exactmarkers/", "peterson7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 142669, 998678), 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/nestedarraywithambiguousindex/", "test.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2, false), 8, 10), 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/soil/", "soil.p", SymmExtractorFailTestOutcome.BreaksRestrictions));

	
		/* Fail tests to check that things like never claims are not supported */
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_never.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_trace.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_notrace.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_accept.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_accept2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_progress.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/FailTests/", "fail_progress2.p", SymmExtractorFailTestOutcome.BreaksRestrictions));
		

		/* Tests for COLLAPSE and MA compression */
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47), "-DCOLLAPSE"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47), "-DMA=37"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 12, 47), "-DCOLLAPSE -DMA=16"));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex10.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 3628800, false), 22, 167), "-DCOLLAPSE"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex10.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 3628800, false), 22, 167), "-DMA=65"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex10.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 3628800, false), 22, 167), "-DCOLLAPSE -DMA=28"));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex15.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1307674368000L, false), 32, 362), "-DCOLLAPSE"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex15.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1307674368000L, false), 32, 362), "-DMA=89"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex15.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 1307674368000L, false), 32, 362), "-DCOLLAPSE -DMA=53"));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex20.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2432902008176640000L, false), 42, 632), "-DCOLLAPSE"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex20.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2432902008176640000L, false), 42, 632), "-DMA=113"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/mutex/fast_basic_swaps/", "mutex20.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 2432902008176640000L, false), 42, 632), "-DCOLLAPSE -DMA=69"));
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DCOLLAPSE"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DMA=73"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DCOLLAPSE -DMA=55"));
		

		
		// Tests for unsupported SPIN compile directives: these should result in a failure when GCC is invoked.
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", SymmReducerFailTestOutcome.GCCCompilationFailure, "-DBFS"));

		
		
		
		// Tests to check that PID-indexed arrays are correctly handled when records are used
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/transpositions/", "reordered_byte.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 117, 395)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/transpositions/", "reordered_int.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 366, 1195)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/transpositions/", "reordered_simple_struct.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 366, 1195)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/transpositions/", "reordered_larger_struct.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 166, 607)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/notranspositions/", "reordered_byte.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 117, 395)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/notranspositions/", "reordered_int.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 366, 1195)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/notranspositions/", "reordered_simple_struct.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 366, 1195)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/misc/pid_indexed_arrays/notranspositions/", "reordered_larger_struct.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 166, 607)));

		
		
		
		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), 40));

		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), "-DNUM_THREADS=4 -lpthread", 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), "-DNUM_THREADS=6 -lpthread", 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), "-DNUM_THREADS=3 -lpthread", 100));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/parallel_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), "-DNUM_THREADS=2 -lpthread", 40));

		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 36255, 141453), "-DNUM_THREADS=4 -lpthread", 100000));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email5.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 120, false), 5666, 21032), "-DNUM_THREADS=6 -lpthread", 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email6.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 720, false), 5361, 23794), "-DNUM_THREADS=3 -lpthread", 100));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email/vector_parallel_enumerate/", "email7.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 5040, false), 296, 5745), "-DNUM_THREADS=2 -lpthread", 40));

		
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_vec_nopar/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951)));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=2 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_nostab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=3 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=4 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/notrans_stab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=5 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=2 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_nostab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=3 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_novec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=4 -lpthread"));
		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/email3/trans_stab_vec_par/", "email3.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 6, false), 3902, 11951), "-DNUM_THREADS=9 -lpthread"));


		testCases.add(new SymmReducerTestCase("TestModels/SymmReducerTests/peterson/vector_flatten/", "peterson4.p", new SymmReducerTestOutcome(new SymmExtractorRunTestOutcome(true, 24, false), 1177, 4706)));


		
		
		

		
		

		
		
		return testCases;
	}
	
	public static void main(String args[]) {
		runTests();
		Tester.displayResults();
	}
	
}

