package src.etch.tests;

public enum SystemErrorTestOutcome implements TestOutcome {
	IOError, FileNotFound;
	
	public boolean matches(TestOutcome actualOutcome) {
		return false;
	}

}
