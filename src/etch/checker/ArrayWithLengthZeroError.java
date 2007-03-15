package src.etch.checker;

import src.etch.error.Error;

public class ArrayWithLengthZeroError extends Error {

	public String message() {
		return "Cannot declare array with length zero";
	}

}
