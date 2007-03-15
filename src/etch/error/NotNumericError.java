package src.etch.error;

public class NotNumericError extends NotTError {

    public NotNumericError(String type, String operator, int nature) {
    	super(type,operator,"numeric",nature);
    }
}
