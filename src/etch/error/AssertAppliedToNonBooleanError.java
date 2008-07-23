package src.etch.error;

public class AssertAppliedToNonBooleanError extends Error {

	private String type;
	
	public AssertAppliedToNonBooleanError(String type) {
		this.type = type;
	}

	@Override
	public String message() {
		return "The assert operator can only be applied to a boolean expression, here it is applied to an expression with type \"" + type + "\"";
	}

}
