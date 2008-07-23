package src.etch.error;

public class LiteralValueTooLargeError extends Error {

	private String badValue;
	
	public LiteralValueTooLargeError(long badValue) {
		this.badValue = String.valueOf(badValue);
	}

	public LiteralValueTooLargeError(String badValue) {
		this.badValue = badValue;
	}
	
	public String message() {
		return "The literal value " + badValue + " is outside the range of values which Promela allows";
	}

}
