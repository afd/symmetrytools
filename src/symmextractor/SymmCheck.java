package src.symmextractor;

import java.io.IOException;

import src.etch.checker.Check;
import src.etch.checker.Checker;
import src.etch.checker.LineCounter;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;

public class SymmCheck extends Check {

	public SymmCheck(String sourceName) throws ParserException, IOException,
			LexerException {
		super(sourceName);
	}
	
	@Override
	protected Checker getChecker(LineCounter lineCounter) {
		return new SymmetryChecker(lineCounter.numberOfLines());
	}


}
