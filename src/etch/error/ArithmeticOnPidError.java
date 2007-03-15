package src.etch.error;

public class ArithmeticOnPidError extends Error {

	public String message() {
		return "error -- variable with pid type used in arithmetic expression";
	}

}
