package src.symmextractor.error;

import src.etch.error.Error;

public class ActiveProctypeError extends Error {

	private String proctypeName;
	
	public ActiveProctypeError(String proctypeName) {
		this.proctypeName = proctypeName;
	}

	@Override
	public String message() {
		return "TopSPIN does not currently support active proctypes.  Consider remodelling your specification to run instances of \"" + proctypeName + "\" via the \"init { atomic { ... } }\" block";
	}

}
