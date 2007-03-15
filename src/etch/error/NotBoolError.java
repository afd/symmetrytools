package src.etch.error;

public class NotBoolError extends NotTError {

    public NotBoolError(String type, String operator, int nature) {
    	super(type,operator,"\"bool\"",nature);
    }
}
