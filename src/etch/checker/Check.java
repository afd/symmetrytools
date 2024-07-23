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
import java.util.StringTokenizer;

import src.etch.typeinference.ConstraintSet;
import src.etch.typeinference.Substituter;
import src.etch.typeinference.Unifier;
import src.etch.types.EtchTypeFactory;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.utilities.BooleanOption;
import src.utilities.CommandLineSwitch;
import src.utilities.Config;
import src.utilities.Location;
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
		
		Lexer lexer = new Lexer(new PushbackReader(br, 1024));
		Parser parser = new Parser(lexer);
		try {
			ProgressPrinter.println("\nParsing input specification...\n");
			
			theAST = parser.parse();
		} catch (ParserException e) {
			if(Config.TESTING_IN_PROGRESS) {
				throw e;
			} else {
				displayParserException(e);
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

	private void displayParserException(ParserException e) {
		int line;
		int column;
		
		StringTokenizer strTok = new StringTokenizer(e.getMessage(), "[,] ");
		line = Integer.parseInt(strTok.nextToken());
		column = Integer.parseInt(strTok.nextToken());
		
		String actualFile;
		int actualLine;
		
		Location location = Config.locations.get(line);
		if(null == location)
		{
			actualFile = "\"" + sourceName + "\"";
			actualLine = line;
		} else {
			actualFile = location.getFile();
			actualLine = location.getLine();
		}
		
		System.out.println("Error at " + actualFile + ", line " + actualLine + ", column " + column + ":");
			
		System.out.print("   next token(s) expected:");
		
		StringTokenizer strTok2 = new StringTokenizer(e.getMessage(), " ");
		boolean outputting = false;
		while(strTok2.hasMoreTokens())
		{
			String tok = strTok2.nextToken();
			if(tok.equals("expecting:"))
			{
				outputting = true;
			} else if(outputting) {
				System.out.print(" " + tok);
			}
		}
		assert(outputting);
		System.out.println("");

		System.out.println("   token found: " + e.getToken() + "\n");
		
	}

	public static BufferedReader getBufferForInputSpecification(String sourceName) throws FileNotFoundException {
		
		Config.locations.clear();
		
		// Check that the source really exists!
		try {
			new FileReader(sourceName);
		} catch(FileNotFoundException e) {
			throw e;
		}

		BufferedReader br = null;
		try {
			
			String cppCommand = (Config.commandLineSwitchIsSet(CommandLineSwitch.CPP) ? Config.getCommandLineSwitchValue(CommandLineSwitch.CPP) : "cpp")
					+ " -D__TOPSPIN__ ";

			if(Config.isOSWindows()) {
				cppCommand += "\"";
			}

			cppCommand += sourceName;

			if(Config.isOSWindows()) {
				cppCommand += "\"";
			}
			
			Process cpp = Runtime.getRuntime().exec(cppCommand);

			BufferedReader cppReader = new BufferedReader(new InputStreamReader(cpp.getInputStream()));
			String programForParsing = "";
			String line;
			int lineNumber = -1;
			int absoluteLineNumber = 1;
			String filename = null;
			while((line=cppReader.readLine())!=null) {
				if(line.length() > 0 && line.charAt(0)=='#') {
					StringTokenizer strTok = new StringTokenizer(line, "# ");
					lineNumber = Integer.parseInt(strTok.nextToken());
					filename = strTok.nextToken();
				} else {
					assert(-1 != lineNumber);
					assert(null != filename);
					programForParsing += line + "\n";
					Config.locations.put(absoluteLineNumber, new Location(filename, lineNumber));
					absoluteLineNumber++;
					lineNumber++;
				}
				
			}
			br = new BufferedReader(new StringReader(programForParsing));
			
			if (cpp.waitFor() != 0) {
				throw new RuntimeException("Error running C preprocessor.");
			}

		} catch (IOException e) {
			System.out.println("C preprocessor (cpp) not available - " + Config.TOOL_NAME + " will not work correctly on files which use #define or #include.");
			System.out.println("If you are using Cygwin under Windows, then perhaps cpp.exe is a symbolic link.  If this is the case then you need to run " + Config.TOOL_NAME + " with the option: -cpp <link target>, where <link target> is the target for the symbolic link, given" +
				" in Windows form.  So, for example, if cpp.exe is a link to /etc/alternatives/cpp.exe, you should use the option -cpp C:\\\\cygwin\\\\etc\\\\alternatives\\\\cpp.exe.  This is a limitation of " + Config.TOOL_NAME + " which the designers hope to fix in a future release.");
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
				System.err.println(chk.getErrorTable().output("while processing " + sourceName, sourceName));
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
		return new Checker(new EtchTypeFactory(), new ConstraintSet(new Unifier()));
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
		Config.TOOL_NAME = "Etch";
		
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
