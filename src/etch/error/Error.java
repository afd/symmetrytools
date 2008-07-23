package src.etch.error;

public abstract class Error {

	public final static int LEFT = 0;
	public final static int RIGHT = 1;
	public final static int UNARY = 2;

	public abstract String message();

	// UN-COMMENT CONSTRUCTOR TO ENABLE CRASH-ON-ERROR
	// FOR DEBUGGING PURPOSES
	
/*	public Error() {

		System.out.println("Crashing on error: " + getClass());
			
		try {
			throw new Exception();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		System.exit(1);

	}
*/	

}
