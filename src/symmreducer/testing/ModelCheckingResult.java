package src.symmreducer.testing;

public class ModelCheckingResult {

	private int numberOfStates;
	private int numberOfTransitions;
	private int exitValue;
	
	public ModelCheckingResult(int exitValue, int numberOfStates, int numberOfTransitions) {
		this.exitValue = exitValue;
		this.numberOfStates = numberOfStates;
		this.numberOfTransitions = numberOfTransitions;
	}

	public int getNumberOfStates() {
		return numberOfStates;
	}

	public int getNumberOfTransitions() {
		return numberOfTransitions;
	}

	public int getExitValue() {
		return exitValue;
	}
}
