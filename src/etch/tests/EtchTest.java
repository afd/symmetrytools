package src.etch.tests;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PushbackReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

import src.etch.checker.Checker;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;

public class EtchTest {

	enum TestResult {
		WellTyped, BadlyTyped, LexerError, ParserError, IOError, FileNotFound, EtchFailure;
	}
	
	public static TestResult runEtchTest(String sourceName) {

		BufferedReader br = null;
		try {
			Process p = Runtime.getRuntime().exec("cpp " + sourceName);
			BufferedReader cppReader = new BufferedReader(new InputStreamReader(p.getInputStream()));
			String programForParsing = "";
			String line;
			int currentLine = 1;
			while((line=cppReader.readLine())!=null) {
				if(line.length() > 0 && line.charAt(0)=='#') {
					String[] splitOnSpace = line.split(" ");
					int nextLine = Integer.parseInt(splitOnSpace[1]);
					for(;currentLine<nextLine; currentLine++) {
						programForParsing += "\n";
					}
				} else {
					programForParsing += line + "\n";
					currentLine++;
				}
				
			}
			br = new BufferedReader(new StringReader(programForParsing));
		} catch (IOException e) {
			System.out.println("C preprocessor not available");
			try {
				br = new BufferedReader(new FileReader(sourceName));
			} catch (FileNotFoundException e1) {
				return TestResult.FileNotFound;
			}
		}
		
		try {
			Lexer scanner = new Lexer(new PushbackReader(br, 1024));
			Parser parser = new Parser(scanner);
			Node theAST;
			theAST = parser.parse();
			Checker checker = new Checker(false);
			theAST.apply(checker);
			checker.unify();
			if(checker.getErrorTable().hasErrors()) {
				return TestResult.BadlyTyped;
			}
			return TestResult.WellTyped;
			
		} catch (LexerException e) {
			return TestResult.LexerError;
		} catch (ParserException e) {
			return TestResult.ParserError;
		} catch (IOException e) {
			return TestResult.IOError;
		} catch (Exception e) {
			return TestResult.EtchFailure;
		}
	}

	public static void main(String args[]) throws IOException {

		String parseFailTests [] = {
				"parsefailunlesswithsemi.p",
				"parsefaillabelthendecl.p",
		};
		
		String failTests [] = {   
				"failbadchannel.p",
				"failduplicatechannelname.p", 
				"failbadchannelassign.p", 
				"failduplicatename.p", 
				"failbadrunargument.p",
				"faillabelusesvarname.p", 
				"failbuggysmall.p",
				"failmultiplelabels.p", 
				"failbuggytelephone.p",
				"failreallycrazyrecursive.p", 
				"failbuggytelephone2.p",
				"failrecursivetypeerror.p", 
				"failchanneldoesnotexist.p",
				"failsillychannel.p", 
				"failchannelerror.p",
				"failsmalltest.p", 
				"failcontrivedrecursive.p",
				"failundefinedlabel.p", 
				"failcrazyrecursive.p",
				"failundefinedlabel2.p",
				"failbadtypedeflookup.p",
				"failbadtypedeflookup2.p",
				"failbadtypedeflookup3.p",
				"failbytesentinsteadofmytpe.p",
				"failmtypemixedupwithchannel.p",
				"failchannelinplaceofbyte.p",
				"failnosubtyperelation.p",
				"faillabelinunless.p",
				"faillabelbeforeunless.p"
		};
		
		String passTests [] = {
				"testbraces.p",
				"testgoodtypedeflookup3.p",
				"testunlesswithdecl.p",
				"testgooddeclaration.p",
				"testsimple.p",
				"testgoodtypedeflookup.p",
				"testtelephone.p",
				"testgoodtypedeflookup2.p",
				"testunless.p",
				"testatomicatomic.p",
				"testdstepdstep.p",
				"testpreprocessormultiline.p",
				"testlabelatomicnoseparator.p",
				"testgoodlabelinunless.p",
				"testanothertelephone.p",
				"testmisc.p",
				"testpotsmodel.p",
				"testresourceallocator.p",
				"testemail.p",
				"testmisc2.p",
				"testpotsmodel2.p",
				"testsharing.p",
				"testloadbalancer.p",
				"testmisc3.p",
				"testpriority.p",
				"testsimpleloadbalancer.p"
		};

		String parsePassTests [] = {
				"hello",  
				"leader2",  
				"mobile1",  
				"pathfinder",  
				"petersonN",
				"snoopy",
				"wordcount",
				"leader",
				"loops",
				"mobile2",
				"peterson",
				"pftp",
				"sort"
		};
		
		List<String> passes = new ArrayList<String>();
		List<String> fails = new ArrayList<String>();
				
		
		for(int i=0; i<parseFailTests.length; i++) {
			TestResult result = runEtchTest("ParseFailTests/" + parseFailTests[i]);
			if(result!=TestResult.ParserError) {
				fails.add(parseFailTests[i] + " - parse fail test, result: " + result);
			} else {
				passes.add(parseFailTests[i] + " - parse fail test");
			}
		}

		for(int i=0; i<failTests.length; i++) {
			TestResult result = runEtchTest("FailTests/" + failTests[i]);
			if(result!=TestResult.BadlyTyped) {
				fails.add(failTests[i] + " - fail test, result: " + result);
			} else {
				passes.add(failTests[i] + " - fail test");
			}
		}
	
		for(int i=0; i<passTests.length; i++) {
			TestResult result = runEtchTest("PassTests/" + passTests[i]);
			if(result!=TestResult.WellTyped) {
				fails.add(passTests[i] + " - pass test, result: " + result);
			} else {
				passes.add(passTests[i] + " - pass test");
			}
		}

		for(int i=0; i<parsePassTests.length; i++) {
			TestResult result = runEtchTest("ParsePassTests/" + parsePassTests[i]);
			if(result!=TestResult.WellTyped && result!=TestResult.BadlyTyped) {
				fails.add(parsePassTests[i] + " - parse pass test, result: " + result);
			} else {
				passes.add(parsePassTests[i] + " - parse pass test");
			}
		}

		System.out.println("Test results:\n\nPASSES\n======");
		for(int i=0; i<passes.size(); i++) {
			System.out.println("   " + passes.get(i));
		}
		System.out.println("\nFAILS\n=====");
		for(int i=0; i<fails.size(); i++) {
			System.out.println("   " + fails.get(i));
		}
		System.out.println("\nSummary:\n   " + passes.size() + " passes\n   " + fails.size() + " fails.\n");
	
		
	}

}
