package src.etch.testing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import src.etch.types.TypeTest;
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

	private static List<TestCase> getTestCases() {
		List<TestCase> testCases = new ArrayList<TestCase>();
		Set<TestCase> missingFeatureTestCases = new HashSet<TestCase>();

		runUnitTests();
		
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

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_eval_1.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_eval_2.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_eval_3.p", EtchTestOutcome.WellTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_eval_1.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_eval_2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_eval_3.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_type_does_not_exist.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_array_index_1.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_array_index_2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_array_index_3.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_array_index_4.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_mtype_name_already_exists.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_mtype_name_already_exists2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_mtype_name_already_exists3.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_proctype_does_not_exist.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_too_few_args_for_proctype.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_too_many_args_for_proctype.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testbitwiseoperations.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failnegationofnonboolean.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbitwisenegationofnonnumeric.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchanoponnonchannel1.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchanoponnonchannel2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchanoponnonchannel3.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failchanoponnonchannel4.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/faillengthofnonchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failsendonnonchannel.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failreceiveonnonchannel.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_goto_refers_to_typename.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_label_name_already_exists.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_variable_name_already_exists.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_literal_value_too_large.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_literal_value_too_large_2.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_simple_statement_not_boolean.p", EtchTestOutcome.BadlyTyped));
						
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_logical_and_applied_to_non_boolean.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_proctype_name_already_used.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_shift_operations.p", EtchTestOutcome.WellTyped));
				
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failarraywithlengthzero.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtypeinferencefornumericchannels.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtypeinferenceforrecords.p", EtchTestOutcome.WellTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferencefornumericchannels.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferenceforrecoreds.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtypinferencemisc2.p", EtchTestOutcome.WellTyped));
				
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferencemisc.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferencesubtypingerror.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferenceincompatibleerror.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failtypeinferencearrays.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testtypeinferencearrays.p", EtchTestOutcome.WellTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testmisc4.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testmultidimarray.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testchannelexpression.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testrecordfieldexpression.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failrecordexpression.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failrecordexpression2.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_conditional.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_conditional2.p", EtchTestOutcome.WellTyped));
	
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_assert_non_bool.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_attempt_at_function_pointer.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_array_index_5.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_eq.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_bad_send.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_conditional.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_conditional2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_ill_formed_inline.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_ill_formed_inline2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_inconsistent_channel_usage.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_inline_with_duplicate_arg_names.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_macro_badly_typed.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_macro_used_with_wrong_num_args.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_missing_run.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_not_bool.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_not_numeric.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_type_used_as_variable.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_variable_not_array.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_variable_not_defined.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_variable_not_record.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadinlinemacro.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failnamealreadyusedasinline.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadinlines.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadinlines2.p", EtchTestOutcome.BadlyTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failbadinlines3.p", EtchTestOutcome.BadlyTyped));
		
		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/failemailmissingchanneltwo.p", EtchTestOutcome.BadlyTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/testanothertelephone.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_engine3F99.p", EtchTestOutcome.WellTyped));

		testCases.add(new EtchTestCase("TestModels/EtchTesting/FailTests/fail_protype_with_duplicate_args_names.p", EtchTestOutcome.BadlyTyped));
				
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_misc.p", EtchTestOutcome.WellTyped));
		testCases.add(new EtchTestCase("TestModels/EtchTesting/PassTests/test_funny_semi_colons.p", EtchTestOutcome.WellTyped));
		
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/sharing.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/faillabelbeforeunless.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/testpotsmodel2.p", EtchTestOutcome.WellTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/faillabelinunless.p", EtchTestOutcome.BadlyTyped));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/wordcount",  EtchTestOutcome.ParsePass));
		missingFeatureTestCases.add(new EtchTestCase("TestModels/EtchTesting/MissingFeatures/fail_bad_use_of_local_keyword.p", EtchTestOutcome.BadlyTyped));
		
		return testCases;
	}

	private static void runUnitTests() {
		TypeTest t = new TypeTest();

		try {
			t.testNameOfRecursiveType();
			t.testNameOfArrayType();
		} catch(Exception e) {
			System.out.println("Etch unit test failed: ");
			e.printStackTrace();
			System.exit(1);
		}
	}

}
