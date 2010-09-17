package src.etch.error;

import src.etch.typeinference.Substituter;
import src.utilities.Config;
import src.utilities.Location;



class ErrorTableEntry {

	private int line;

	private Error error;

	public ErrorTableEntry(int line, Error error) {
		this.line = line;
		this.error = error;
	}

	public String output(String sourceName) {
		String file;
		int actualLine;
		Location location = Config.locations.get(line);
		if(null != location) {
			file = location.getFile();
			actualLine = location.getLine();
		} else {
			file = "\"" + sourceName + "\"";
			actualLine = line;
		}
		
		return "Error" + " at " + file + ", line " + actualLine + ":\n   " + error.message();
	}

	public void applySubstitutions(Substituter substituter) {
		error.applySubstitutions(substituter);
	}

}
