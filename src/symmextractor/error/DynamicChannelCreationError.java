package src.symmextractor.error;

import src.etch.error.Error;

public class DynamicChannelCreationError extends Error {

	private String channel;
	private boolean declarationOccursInTypedef;
	
	public DynamicChannelCreationError(String channel, boolean declarationOccursInTypedef) {
		this.channel = channel;
		this.declarationOccursInTypedef = declarationOccursInTypedef;
	}

	@Override
	public String message() {
		String result = "TopSPIN does not currently support channel initialisation inside ";
		if(declarationOccursInTypedef) {
			return result + "user-defined types.  Consider removing field \"" + channel + "\" from the type, and using equivalent global channels instead";
		} else {
			return result + "proctype bodies.  Consider making \"" + channel + "\" a proctype parameter, and globally declaring channels to be passed as this parameter";
		}
	}

}
