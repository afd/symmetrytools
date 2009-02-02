package src.etch.error;

import src.etch.types.Type;

public class NotNumericError extends NotTError {

    public NotNumericError(Type type, String operator, int nature, String variableName) {
    	super(type, operator,"numeric", nature, variableName);
    }
    
    public NotNumericError(Type type, String operator, int nature) {
    	this(type, operator, nature, null);
    }

}
