package src.etch.testing;

import src.testing.TestOutcome;

public enum EtchTestOutcome implements TestOutcome {
	WellTyped, BadlyTyped, LexerError, ParserError, EtchFailure, ParsePass;

	public boolean matches(TestOutcome actualOutcome) {

		switch(this) {

		case ParsePass: return actualOutcome == WellTyped || actualOutcome == BadlyTyped;

		default: return this == actualOutcome;
		}
	}

}

