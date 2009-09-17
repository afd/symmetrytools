/****************************************************************************/
/*                 ETCH: An Enhanced Type Checker for Promela               */
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : Main.java                                                */
/* DESCRIPTION   : Top-level driver for ETCH                                */
/****************************************************************************/

package src.etch.checker;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PushbackReader;
import java.io.StringReader;

import src.etch.typeinference.Substituter;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.utilities.BooleanOption;
import src.utilities.CommandLineSwitch;
import src.utilities.Config;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;

public class Check {


	/** The AST representing the source program. */
	protected Node theAST;
	protected String sourceName;
	
	public Check(String sourceName) throws ParserException, IOException, LexerException {
		
		if(Config.profiling()) { Profile.PARSE_START = System.currentTimeMillis(); }

		this.sourceName = sourceName;

		BufferedReader br = null;
		try {
			br = getBufferForInputSpecification(sourceName);
		} catch (FileNotFoundException e) {
			ProgressPrinter.println("Cannot access source file " + sourceName);
			if(Config.TESTING_IN_PROGRESS) {
				throw e;
			} else {
				System.exit(1);
			}
		}
		
		try {
			theAST = new Parser(new Lexer(new PushbackReader(br, 1024))).parse();
		} catch (ParserException e) {
			if(Config.TESTING_IN_PROGRESS) {
				throw e;
			} else {
				e.printStackTrace();
				System.exit(1);
			}
		} catch (LexerException e) {
			if(Config.TESTING_IN_PROGRESS) {
				throw e;
			} else {
				e.printStackTrace();
				System.exit(1);
			}
		} catch (IOException e) {
			if(Config.TESTING_IN_PROGRESS) {
				throw e;
			} else {
				e.printStackTrace();
				System.exit(1);
			}
		}
		
		if(Config.profiling()) { Profile.PARSE_END = System.currentTimeMillis(); }

	}

	public static BufferedReader getBufferForInputSpecification(String sourceName) throws FileNotFoundException {
		
		// Check that the source really exists!
		try {
			new FileReader(sourceName);
		} catch(FileNotFoundException e) {
			throw e;
		}

		BufferedReader br = null;
		try {

			String cppCommand = "cpp ";
			
			if(Config.isOSWindows()) {
				cppCommand += "\"";
			}

			cppCommand += sourceName;

			if(Config.isOSWindows()) {
				cppCommand += "\"";
			}
			
			Process cpp = Runtime.getRuntime().exec(cppCommand);

/*			ErrorStreamHandler errorHandler = new ErrorStreamHandler(cpp, "\ncpp produced errors:\n======================",  "End of cpp errors", true);
			errorHandler.start();*/
			
			BufferedReader cppReader = new BufferedReader(new InputStreamReader(cpp.getInputStream()));
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
			
			cpp.waitFor();
			
/*			if(0 != cpp.exitValue()) {
				System.out.println("C preprocessor (cpp) exited with error code " + cpp.exitValue() + ".  TopSPIN will run on un-preprocessed file, and will not work correctly on files which use #define or #include.");
				br = new BufferedReader(new FileReader(sourceName));
			}*/
			
		} catch (IOException e) {
			System.out.println("C preprocessor (cpp) not available - TopSPIN will not work correctly on files which use #define or #include.");
			br = new BufferedReader(new FileReader(sourceName));
		} catch (InterruptedException e) {
			System.out.println("C preprocessor (cpp) was interrupted.  TopSPIN will run on un-preprocessed file, and will not work correctly on files which use #define or #include.");
			br = new BufferedReader(new FileReader(sourceName));
		}
		return br;
	}

	public boolean typecheck() {
		ProgressPrinter.println("\nTypechecking input specification...\n");

		LineCounter lineCounter = new LineCounter();
		theAST.apply(lineCounter);
		
		Checker chk = getChecker(lineCounter);
		theAST.apply(chk);
		Substituter substituter = chk.unify();
	
		substituter.setTypeInformation(chk);

		if (chk.getErrorTable().hasErrors()) {

			if(Config.TESTING_IN_PROGRESS || !Config.inQuietMode()) {
				chk.getErrorTable().applySubstitutions(substituter);
				System.err.println(chk.getErrorTable().output("while processing " + sourceName));
			}

			return false;
		}

		theAST.apply(substituter);
		
		ProgressPrinter.println("Specification is well typed!");

		if(Config.inVerboseMode()) {
			System.out.println(chk.showCompleteTypeInformation(sourceName));
		}

		return true;
	}

	protected Checker getChecker(LineCounter lineCounter) {
		return new Checker();
	}

	
	private static void processHelpArguments(String[] args) {
		
		final String ETCH_VERSION = "1.0";
		
		assert(args.length>0);

		System.out.println("\nEtch version " + ETCH_VERSION);
		if(args.length==1) {
			System.out.println("\nUse 'help' followed by name of command-line option for summary of what the option does.\n");

			System.out.println("Available options:\n");

			for(CommandLineSwitch option : CommandLineSwitch.values()) {
				if((CommandLineSwitch.CHECK) != option && (CommandLineSwitch.DETECT != option)) {
					System.out.println("  -" + option.toString().toLowerCase());
				}
			}
			
		} else {
			Config.showHelpForConfigurationOption(args[1], true);
		}
	}
	
	
	public static void main(String[] args) throws ParserException, IOException, LexerException {

		Config.resetConfiguration();
		
		if((args.length > 0) && (args[0].toUpperCase().equals("HELP"))) {
			processHelpArguments(args);
			System.exit(0);
		}

		Config.setUnspecifiedOptionsToDefaultValues();
		Config.initialiseCommandLineSwitches();
		Config.setBooleanOption(BooleanOption.VERBOSE, true);

		int currentArg = Config.processCommandLineSwitches(args);
				
		if(currentArg >= args.length) {
			System.out.println("Error: no input file specified.\n");
			System.out.println("To run Etch on an input file:\n" +
					           "    [command-line options] <inputfile>\n" +
							   "For help on command-line option:\n" +
							   "    help <option>\n" +
							   "For list of options:\n" +
							   "    help\n");
			System.exit(1);
		}
				
		new Check(args[currentArg]).typecheck();
	}	
}
