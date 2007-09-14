package src.etch.error;


public class ArrayWithLengthZeroError extends Error {

	public String message() {
		return "Cannot declare array with length zero";
	}

}
