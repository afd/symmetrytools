package src.etch.error;

public abstract class NotTError extends Error {

	protected String type;
	protected String operator;
	protected String correctType;
	protected int nature;

	public NotTError(String type, String operator, String correctType, int nature) {
		this.type = type;
		this.operator = operator;
		this.correctType = correctType;
		this.nature = nature;
	}
	
	public String message() {
		String result = "the ";
		if(nature == LEFT) {
			result = result + "first ";
		}
		else if(nature == RIGHT) {
			result = result + "second ";
		}
		return result + "argument of " + operator + " should have " + correctType + " type, but here it is \"" + type + "\"";
	}

}
