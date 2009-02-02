package src.etch.error;

import src.etch.typeinference.Substituter;



class ErrorTableEntry {

	private int line;

	private Error error;

	public ErrorTableEntry(int line, Error error) {
		this.line = line;
		this.error = error;
	}

	public String output() {
		return "Error" + " at line " + line + ": " + error.message();
	}

	public void applySubstitutions(Substituter substituter) {
		error.applySubstitutions(substituter);
	}

}
