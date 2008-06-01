package src.testing;


public enum SystemErrorTestOutcome implements TestOutcome {
	IOError, FileNotFound, InterruptedError, BadConfigurationFile, NoConfigurationFileFound;
	
	public boolean matches(TestOutcome actualOutcome) {
		return false;
	}

}
