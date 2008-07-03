package src.etch.error;

public abstract class Error {

	public final static int LEFT = 0;
	public final static int RIGHT = 1;
	public final static int UNARY = 2;

	public abstract String message();

	// Change to true for debugging
	private boolean crashOnError = false;
	
	public Error() {

		if(crashOnError) {

			System.out.println("Crashing on error: " + getClass());
			
			try {
				throw new Exception();
			} catch (Exception e) {
				e.printStackTrace();
			}
			
			System.exit(1);

		}

	}
	

}
