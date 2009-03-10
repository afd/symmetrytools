package src.exceptions;

@SuppressWarnings("serial")
public class BadlyInitialisedVariableException extends Exception {

	private int init;
	private int upper;
	private int lower;

	public BadlyInitialisedVariableException(int lower, int upper, int init) {
		this.lower = lower;
		this.upper = upper;
		this.init = init;
	}
	
	public String toString() {
		return "Variable initialised with value " + init + " which is not in the range ["+lower+".."+upper+"].";
	}
	
}
