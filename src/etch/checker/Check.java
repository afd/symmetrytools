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
import src.symmextractor.SymmetryChecker;
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

	public boolean typecheck(boolean isPidSensitive) {
		ProgressPrinter.println("\nTypechecking input specification...\n");

		LineCounter lineCounter = new LineCounter();
		theAST.apply(lineCounter);
		
		Checker chk = (isPidSensitive ? new SymmetryChecker(lineCounter.numberOfLines()) : new Checker());
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

	public static void main(String[] args) throws ParserException, IOException, LexerException {

		if (args.length < 1) {
			System.out.println("Usage: check filename");
			System.exit(1);
		}

		boolean isPidSensitive = (args.length > 1) && (args[1].equals("-symm"));

		Config.resetConfiguration();
		Config.setUnspecifiedOptionsToDefaultValues();
		
		new Check(args[0]).typecheck(isPidSensitive);
	}
}
