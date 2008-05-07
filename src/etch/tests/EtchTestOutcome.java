package src.etch.tests;

public enum EtchTestOutcome implements TestOutcome {
	WellTyped, BadlyTyped, LexerError, ParserError, EtchFailure, ParsePass;

	public boolean matches(TestOutcome actualOutcome) {

		switch(this) {

		case ParsePass: return actualOutcome == WellTyped || actualOutcome == BadlyTyped;

		default: return this == actualOutcome;
		}
	}

}

