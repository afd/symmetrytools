package src.etch.error;

import java.io.PrintStream;


class ErrorTableEntry {

	private int line;

	private Error error;

	public ErrorTableEntry(int line, Error error) {
		this.line = line;
		this.error = error;
	}

	public String output() {
		if(line==-1) {
			return "Error (line number unknown): " + error.message();
		}
		return "Error" + " at line " + line + ": " + error.message();
	}

	public void output(PrintStream out) {
		out.print(output());
	}

}
