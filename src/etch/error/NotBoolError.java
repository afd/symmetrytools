package src.etch.error;

import src.etch.types.Type;

public class NotBoolError extends NotTError {

    public NotBoolError(Type type, String operator, int nature) {
    	super(type,operator,"\"bool\"",nature);
    }
}
