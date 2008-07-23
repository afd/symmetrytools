package src.etch.error;

public abstract class NotTError extends Error {

	protected String type;
	protected String operator;
	protected String correctType;
	protected int nature;
	private String argumentName;

	public NotTError(String type, String operator, String correctType, int nature, String argumentName) {
		this.type = type;
		this.operator = operator;
		this.correctType = correctType;
		this.nature = nature;
		this.argumentName = argumentName;
	}
	
	public NotTError(String type, String operator, String correctType, int nature) {
		this(type,operator,correctType,nature,null);
	}

	public String message() {
		String result = "";
		
		if(null != argumentName) {
			result += "\"" + argumentName + "\", ";
		}
		
		
		result += "the";
		if(nature == LEFT) {
			result = result + "first";
		}
		else if(nature == RIGHT) {
			result = result + "second";
		}
		result += " argument of " + operator;
		
		if(null != argumentName) {
			result += ","; 
		}

		result += " should have " + correctType + " type, but here it is \"" + type + "\"";
		
		return result;
	}

}
