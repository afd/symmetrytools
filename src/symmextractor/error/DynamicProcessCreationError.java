package src.symmextractor.error;

import src.etch.error.Error;

public class DynamicProcessCreationError extends Error {

	private String proctypeNameForCreatedProcess;
	private String proctypeNameInWhichRunStatementOccurs;
	
	public DynamicProcessCreationError(String proctypeNameForCreatedProcess, String proctypeNameInWhichRunStatementOccurs) {
		this.proctypeNameForCreatedProcess = proctypeNameForCreatedProcess;
		this.proctypeNameInWhichRunStatementOccurs = proctypeNameInWhichRunStatementOccurs;
	}

	@Override
	public String message() {
		return "TopSPIN does not support dynamic process creation.  You could emulate this unsupported feature by " +
				"instantiating a fixed pool of instances of \"" + proctypeNameForCreatedProcess + "\" in the \"init { " +
				"atomic { ... } }\" block, initialised in a sleeping state.  Then instances of \"" + 
				proctypeNameInWhichRunStatementOccurs + "\" can send \"wakeup\" messages to instances of \"" + 
				proctypeNameForCreatedProcess + "\", rather than actually running them";
	}

}
