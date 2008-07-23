package src.etch.error;

public class BadArrayIndexError extends Error {

	private String actualType;
	private String expectedType;
	
	public BadArrayIndexError(String actualType, String expectedType) {
		this.actualType = actualType;
		this.expectedType = expectedType;
	}

	@Override
	public String message() {
		return "Type \"" + actualType + "\" cannot be used as an array index, it is not a subtype of \"" + expectedType + "\"";
	}

}
