package src.etch.error;

import junit.framework.Assert;
import src.etch.checker.LabelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.InlineEntry;

public class JumpToUndefinedLabelError extends Error {

	private String labelName;
	private EnvEntry actualEntry;
	
	public JumpToUndefinedLabelError(String labelName, EnvEntry actualEntry) {
		this.labelName = labelName;
		this.actualEntry = actualEntry;
		Assert.assertFalse(actualEntry instanceof LabelEntry);
	}

	public String message() {
		if(actualEntry==null) {
			return "goto statement refers to undefined label name '" + labelName + "'";
		}
		String result = "goto statement refers to '" + labelName + "', which is declared (on line " + 
			actualEntry.getLineOfDeclaration() + ") as a";
		if(actualEntry instanceof InlineEntry) {
			result += "n";
		}
		result += " " + actualEntry.getEntryKind() + " name";

		return result;
	}

}
