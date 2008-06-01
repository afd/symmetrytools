package src.symmextractor.error;

import src.etch.error.Error;

public class GlobalArrayOfChannelsError extends Error {

	private String name;
	
	public GlobalArrayOfChannelsError(String name) {
		this.name = name;
	}

	public String message() {
		return "\"" + name + "\" is a global array of channels, which is not yet supported by TopSpin.  Consider remodelling to use multiple individual channels instead";
	}

}
