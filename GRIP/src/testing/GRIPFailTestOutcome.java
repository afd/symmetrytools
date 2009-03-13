package src.testing;


public enum GRIPFailTestOutcome implements GRIPTestOutcome {

	ParserError, LexerError, PRISMError, PRISMIOError, ErrorParsingVerificationResult, PRISMInterrupted;

	public boolean matches(TestOutcome actualOutcome) {
		return this == actualOutcome;
	}
	
}
