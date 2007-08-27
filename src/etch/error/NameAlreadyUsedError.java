package src.etch.error;

import src.etch.env.EnvEntry;
import src.etch.env.InlineEntry;

public class NameAlreadyUsedError extends Error {

	String name;
	EnvEntry existingEntry;
	
	public NameAlreadyUsedError(String name, EnvEntry existingEntry) {
		this.name = name;
		this.existingEntry = existingEntry;
	}
	
	public String message() {
		String result = "The name \"" + name + "\" is already used (on line " + existingEntry.getLineOfDeclaration() + ") as a";
		if(existingEntry instanceof InlineEntry) {
			result += "n";
		}
		result += " " + existingEntry.getEntryKind() + " name.";
		return result;
	}

}
