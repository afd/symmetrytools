package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public abstract class NotTError extends Error {

	protected Type type;
	protected String operator;
	protected String correctKindOfType;
	protected int nature;
	private String argumentName;

	public NotTError(Type type, String operator, String correctKindOfType, int nature, String argumentName) {
		this.type = type;
		this.operator = operator;
		this.correctKindOfType = correctKindOfType;
		this.nature = nature;
		this.argumentName = argumentName;
	}
	
	public NotTError(Type type, String operator, String correctKindOfType, int nature) {
		this(type,operator,correctKindOfType,nature,null);
	}

	public String message() {
		String result = "";
		
		if(null != argumentName) {
			result += "\"" + argumentName + "\", ";
		}
		
		
		result += "the ";
		if(nature == LEFT) {
			result = result + "first";
		}
		else if(nature == RIGHT) {
			result = result + "second";
		}
		result += " argument of \"" + operator + "\"";
		
		if(null != argumentName) {
			result += ","; 
		}

		result += " should have " + correctKindOfType + " type, but here it is \"" + Minimiser.minimise(type).name() + "\"";
		
		return result;
	}

    @Override
	public void applySubstitutions(Substituter substituter) {
		type = substituter.applySubstitutions(type);
    }

}
