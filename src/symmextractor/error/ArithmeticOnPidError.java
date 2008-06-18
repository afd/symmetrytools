package src.symmextractor.error;

import src.etch.error.Error;

public class ArithmeticOnPidError extends Error {

	public String message() {
		return "error -- variable with pid type used in arithmetic expression";
	}

}
