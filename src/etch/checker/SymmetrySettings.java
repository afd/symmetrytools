package src.etch.checker;

public class SymmetrySettings {
	
	/* If we are type checking before symmetry reduction then the
	 * number of processes in the specification is vital, as this
	 * defines the literal range for the `pid' type
	 */
	protected static int noProcesses;
	
	/* Records whether or not we are type checking before symmetry
	 * reduction
	 */
	public static boolean CHECKING_SYMMETRY = false;
		
	public static void setNoProcesses(int noProcesses) {
		SymmetrySettings.noProcesses = noProcesses;
	}

	public static int noProcesses() {
		return noProcesses;
	}

}
