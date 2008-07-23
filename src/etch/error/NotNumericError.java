package src.etch.error;

public class NotNumericError extends NotTError {

    public NotNumericError(String type, String operator, int nature, String variableName) {
    	super(type,operator,"numeric",nature, variableName);
    }
    
    public NotNumericError(String type, String operator, int nature) {
    	this(type, operator, nature, null);
    }

}
