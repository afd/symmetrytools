package src.etch.tests;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

public class EtchTester {
	
	public static void main(String args[]) throws IOException {

		System.exit(Tester.runTests(getTestCases()));
						
	}

	private static Set<TopSpinTestCase> getTestCases() {
		Set<TopSpinTestCase> testCases = new HashSet<TopSpinTestCase>();

		testCases.add(new EtchTestCase("ParseFailTests/parsefailunlesswithsemi.p", EtchTestOutcome.ParserError));
		testCases.add(new EtchTestCase("ParseFailTests/parsefaillabelthendecl.p", EtchTestOutcome.ParserError));
		
		testCases.add(new EtchTestCase("FailTests/failbadchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failduplicatechannelname.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failbadchannelassign.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failduplicatename.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failbadrunargument.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/faillabelusesvarname.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failbuggysmall.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failmultiplelabels.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failbuggytelephone.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failreallycrazyrecursive.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failbuggytelephone2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failrecursivetypeerror.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failchanneldoesnotexist.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failsillychannel.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failchannelerror.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failsmalltest.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failcontrivedrecursive.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failundefinedlabel.p", EtchTestOutcome.BadlyTyped)); 
		testCases.add(new EtchTestCase("FailTests/failcrazyrecursive.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failundefinedlabel2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadtypedeflookup.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadtypedeflookup2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadtypedeflookup3.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbytesentinsteadofmytpe.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failmtypemixedupwithchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failchannelinplaceofbyte.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failnosubtyperelation.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/faillabelinunless.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/faillabelbeforeunless.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failmisc.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failmisc2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadrecvargs.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadrecvargs2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadsendargs.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failincorrectloadbalancer.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failbadinlines.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/failemailmissingchanneltwo.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("FailTests/fail_ex_6.p", EtchTestOutcome.BadlyTyped));

				
		testCases.add(new EtchTestCase("PassTests/testbraces.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testgoodtypedeflookup3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testunlesswithdecl.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testgooddeclaration.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testsimple.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testgoodtypedeflookup.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testtelephone.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testgoodtypedeflookup2.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testunless.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testatomicatomic.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testdstepdstep.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testpreprocessormultiline.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testlabelatomicnoseparator.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testgoodlabelinunless.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testanothertelephone.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testpotsmodel.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testresourceallocator.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testemail.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testpotsmodel2.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testsharing.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testloadbalancer.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testmisc3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testpriority.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testsimpleloadbalancer.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testtelephoneexample.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testfirewirestar3.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_ex_6_well_typed.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testsort.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testsplurge.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_mobile1_well_typed.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_mobile2_well_typed.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_engine3F99.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/testassertinnever.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_asg2_assigned.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("PassTests/test_asg2_worked_out.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("ParsePassTests/hello",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/leader2",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("ParsePassTests/mobile1",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("ParsePassTests/pathfinder",  EtchTestOutcome.ParsePass));  
		testCases.add(new EtchTestCase("ParsePassTests/petersonN",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/snoopy",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/wordcount",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/leader",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/loops",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/mobile2",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/peterson",  EtchTestOutcome.ParsePass));
		testCases.add(new EtchTestCase("ParsePassTests/pftp",  EtchTestOutcome.ParsePass));
		return testCases;
	}

}
