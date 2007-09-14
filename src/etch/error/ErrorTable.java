package src.etch.error;

import java.util.ArrayList;
import java.util.List;

public class ErrorTable {

	private List<ErrorTableEntry> messages;

	public ErrorTable() {
		messages = new ArrayList<ErrorTableEntry>();
	}

	// Adds a new error.

	public void add(int line, Error e) {
		messages.add(new ErrorTableEntry(line, e));
	}

	public boolean hasErrors() {
		return !messages.isEmpty();
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
			result = result + getMessage(i).output() + ".\n\n";
		}
		return result;
	}

	public void add(int line, List<String> callStack, Error e) {
		messages.add(new ErrorTableInlineEntry(line, callStack, e));
	}

	int noMessages() {
		return messages.size();
	}

	ErrorTableEntry getMessage(int i) {
		return messages.get(i);
	}

}
