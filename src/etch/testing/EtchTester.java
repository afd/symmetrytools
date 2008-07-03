package src.etch.testing;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import src.testing.TestCase;
import src.testing.Tester;

public class EtchTester {


	public static void runTests() {
		System.out.println("ETCH TESTS");
		System.out.println("==========");
		Tester.runTests(getTestCases());
	}
	
	public static void main(String args[]) throws IOException {
		runTests();
		Tester.displayResults();
	}

	private static Set<TestCase> getTestCases() {
		Set<TestCase> testCases = new HashSet<TestCase>();
		Set<TestCase> missingFeatureTestCases = new HashSet<TestCase>();

		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParseFailTests/parsefailunlesswithsemi.p", EtchTestOutcome.ParserError));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParseFailTests/parsefaillabelthendecl.p", EtchTestOutcome.ParserError));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failduplicatechannelname.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadchannelassign.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failduplicatename.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadrunargument.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/faillabelusesvarname.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbuggysmall.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failmultiplelabels.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbuggytelephone.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failreallycrazyrecursive.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbuggytelephone2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failrecursivetypeerror.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchanneldoesnotexist.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failsillychannel.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchannelerror.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failsmalltest.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failcontrivedrecursive.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failundefinedlabel.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failcrazyrecursive.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failundefinedlabel2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadtypedeflookup.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadtypedeflookup2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadtypedeflookup3.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbytesentinsteadofmytpe.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failmtypemixedupwithchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchannelinplaceofbyte.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failnosubtyperelation.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failmisc.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failmisc2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadrecvargs.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadrecvargs2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadsendargs.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failincorrectloadbalancer.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_ex_6.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failpriority.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_ex_6_badly_typed.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/bad_resourceallocator.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failpotsmodel.p", EtchTestOutcome.BadlyTyped));
				
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testbraces.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testgoodtypedeflookup3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testunlesswithdecl.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testgooddeclaration.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testsimple.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testgoodtypedeflookup.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtelephone.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testgoodtypedeflookup2.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testunless.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testatomicatomic.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testdstepdstep.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testpreprocessormultiline.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testlabelatomicnoseparator.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testgoodlabelinunless.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testpotsmodel.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testresourceallocator.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testemail.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testloadbalancer.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testmisc3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testpriority.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testsimpleloadbalancer.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtelephoneexample.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testfirewirestar3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_ex_6_well_typed.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testsort.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testsplurge.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_mobile2_well_typed.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testassertinnever.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_asg2_assigned.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_asg2_worked_out.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/hello",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/leader2",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/mobile1",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/pathfinder",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/petersonN",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/snoopy",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/leader",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/loops",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/mobile2",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/peterson",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParsePassTests/pftp",  EtchTestOutcome.ParsePass));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/ParseFailTests/misc1.p",  EtchTestOutcome.ParserError));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failfielddoesnotexist.p",  EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/SymmExtractorTests/BadlyTyped/failincrementpid.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/SymmExtractorTests/BadlyTyped/faildecrementpid.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_mod.p", EtchTestOutcome.WellTyped));
				
		
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/sharing.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/faillabelbeforeunless.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/testpotsmodel2.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/test_engine3F99.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/testanothertelephone.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/faillabelinunless.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/wordcount",  EtchTestOutcome.ParsePass));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/failbadinlines.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/failbadinlines2.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/failbadinlines3.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/failemailmissingchanneltwo.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/fail_bad_use_of_local_keyword.p", EtchTestOutcome.BadlyTyped));
		
		return testCases;
	}

}
