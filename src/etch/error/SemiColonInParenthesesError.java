package src.etch.error;

public class SemiColonInParenthesesError extends Error {

	@Override
	public String message() {
		return "Token \";\" has been used within parenthesis";
	}

}
