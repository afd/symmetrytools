package src.etch.testing;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PushbackReader;

import src.etch.checker.Check;
import src.etch.checker.Checker;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.testing.SystemErrorTestOutcome;
import src.testing.TestCase;
import src.testing.TestOutcome;

public class EtchTestCase extends TestCase {

	public EtchTestCase(String filename, EtchTestOutcome outcome) {
		super(filename, outcome);
	}

	@Override
	public void run() {

		BufferedReader br = null;
		try {
			br = Check.getBufferForInputSpecification(filename);
			Node theAST = new Parser(new Lexer(new PushbackReader(br, 1024))).parse();
			Checker checker = new Checker();
			theAST.apply(checker);
			checker.unify();
			if(checker.getErrorTable().hasErrors()) {				
				actualOutcome = EtchTestOutcome.BadlyTyped;
			} else {
				actualOutcome = EtchTestOutcome.WellTyped;
			}
		} catch (LexerException e) {
				actualOutcome = EtchTestOutcome.LexerError;
		} catch (ParserException e) {
				actualOutcome = EtchTestOutcome.ParserError;
		} catch (FileNotFoundException e) {
			actualOutcome = SystemErrorTestOutcome.FileNotFound;
		} catch (IOException e) {
				actualOutcome = SystemErrorTestOutcome.IOError;
		} catch (Exception e) {
			e.printStackTrace();
				actualOutcome = EtchTestOutcome.EtchFailure;
		}
		
	}

	public TestOutcome getOutcome() {
		return actualOutcome;
	}

}
