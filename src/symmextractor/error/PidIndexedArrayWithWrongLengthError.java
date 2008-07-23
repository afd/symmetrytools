package src.symmextractor.error;

import src.etch.error.Error;


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
		return "pid-indexed array " + arrayName + " declared with length " + arrayLength + " instead of " + (noProcesses+1);
	}

}
