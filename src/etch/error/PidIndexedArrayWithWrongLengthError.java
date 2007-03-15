package src.etch.error;


public class PidIndexedArrayWithWrongLengthError extends Error {

	private String arrayName;
	private int arrayLength;
	private int noProcesses; 
	
	public PidIndexedArrayWithWrongLengthError(String arrayName, int arrayLength, int noProcesses) {
		this.arrayName = arrayName;
		this.arrayLength = arrayLength;
		this.noProcesses = noProcesses;
	}

	public String message() {
		return "error: pid-indexed array " + arrayName + " declared with length " + arrayLength + " instead of " + (noProcesses+1);
	}

}
