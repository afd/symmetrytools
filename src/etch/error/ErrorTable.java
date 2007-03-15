package src.etch.error;

import java.util.*;
import java.io.*;

public class ErrorTable {

	private Vector<ErrorTableEntry> errors;

	public ErrorTable() {
		errors = new Vector<ErrorTableEntry>();
	}

	// Adds a new error.

	public void add(int line, Error e) {
		errors.addElement(new ErrorTableEntry(line, e));
	}

	public boolean hasErrors() {
		return !(errors.isEmpty());
	}

	public void output(PrintStream out, String header) {
		int numErrors = errors.size();
		out.print(numErrors);
		out.println(" errors were found " + header + ":");
		out.println();
		Enumeration errs = errors.elements();
		while (errs.hasMoreElements()) {
			((ErrorTableEntry) errs.nextElement()).output(out);
			out.println();
		}
	}

	public String output(String header) {
		String result = "";
		int numErrors = errors.size();
		result = result + numErrors + " errors were found " + header + ":\n\n";
		Enumeration errs = errors.elements();
		while (errs.hasMoreElements()) {
			result = result + ((ErrorTableEntry) errs.nextElement()).output() + "\n\n";
		}
		return result;
	}

	public void add(int line, List<String> callStack, Error e) {
		errors.addElement(new ErrorTableInlineEntry(line, callStack, e));
	}
	
}
