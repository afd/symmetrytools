package src.etch.error;

import java.io.*;

public class ErrorTableEntry {

	private int line;

	private Error err;

	public ErrorTableEntry(int l, Error e) {
		line = l;
		err = e;
	}

	public void output(PrintStream out) {
		out.print(output());
	}

	public String output() {
		if(line==-1) {
			return "Error: " + err.message();
		}
		return "Line " + line + ": Error: " + err.message();
	}

}
