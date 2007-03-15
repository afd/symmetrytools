package src.etch.error;

public abstract class Error {

	public static int LEFT = 0;
	public static int RIGHT = 1;
	public static int UNARY = 2;
	
    public abstract String message();

}
