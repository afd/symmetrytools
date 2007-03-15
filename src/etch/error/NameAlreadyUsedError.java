package src.etch.error;

import src.etch.env.EnvEntry;

public class NameAlreadyUsedError extends Error {

	String name;
	EnvEntry existingEntry;
	
	public NameAlreadyUsedError(String name, EnvEntry existingEntry) {
		this.name = name;
		this.existingEntry = existingEntry;
	}
	
	public String message() {
		return "The name \"" + name + "\" is already used as a " + existingEntry + " name.";
	}

}
