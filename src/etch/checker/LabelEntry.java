package src.etch.checker;

import src.etch.env.EnvEntry;

public class LabelEntry extends EnvEntry {

	public LabelEntry(int lineOfDeclaration) {
		super(lineOfDeclaration);
	}

	public String toString() {
		return " label";
	}

	public String getEntryKind() {
		return "label";
	}

}
