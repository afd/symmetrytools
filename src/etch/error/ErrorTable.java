package src.etch.error;

import java.util.*;
import java.io.*;

public class ErrorTable extends FeedbackTable {

	public ErrorTable() {
		super();
	}

	// Adds a new error.

	public void add(int line, Error e) {
		super.add(new ErrorTableEntry(line, e));
	}

	public boolean hasErrors() {
		return hasFeedback();
	}

	public String output(String header) {
		String result = noMessages() + " error";
		if(noMessages()==1) {
			result += " was";
		} else {
			result += "s were";
		}
		result += " found " + header + ":\n\n";
		for(int i=0; i<noMessages(); i++) {
			result = result + getMessage(i).output() + "\n\n";
		}
		return result;
	}

	public void add(int line, List<String> callStack, Error e) {
		super.add(new ErrorTableInlineEntry(line, callStack, e));
	}
	
}
