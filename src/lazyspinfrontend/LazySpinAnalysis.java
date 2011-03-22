package src.lazyspinfrontend;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PushbackReader;

import src.etch.checker.Check;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.utilities.BooleanOption;
import src.utilities.Config;
import src.utilities.ProgressPrinter;

public class LazySpinAnalysis {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		if(args.length != 1)
		{
			System.out.println("Error - usage: LazySpinAnalysis <file>");
			System.exit(1);
		}
				
		final String sourceName = args[0];

		Config.resetConfiguration();
		Config.setUnspecifiedOptionsToDefaultValues();
		Config.initialiseCommandLineSwitches();
		Config.setBooleanOption(BooleanOption.VERBOSE, true);
		
		BufferedReader br = null;
		try {
			br = Check.getBufferForInputSpecification(sourceName);
		} catch (FileNotFoundException e) {
			ProgressPrinter.println("Cannot access source file " + sourceName);
			System.exit(1);
		}
		
		Node theAST = null;
		
		try {
			theAST = new Parser(new Lexer(new PushbackReader(br, 1024))).parse();
		} catch (ParserException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (LexerException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
		
		theAST.apply(new LazySpinRepGenerator());

		System.out.println("Parsed successfully.");
	}

}
