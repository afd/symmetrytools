package src.etch.error;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

public class ErrorTableInlineEntry extends ErrorTableEntry {

	private List<String> callStack;
	
	public ErrorTableInlineEntry(int line, List<String> callStack, Error e) {
		super(line,e);
		this.callStack = new ArrayList<String>(callStack.size());
		for(int i=0; i<callStack.size(); i++) {
			this.callStack.add(callStack.get(i));
		}
	}
	
	public void output(PrintStream out) {
		out.print(output());
	}

	public String output() {
		String result = super.output();
		for(int i=callStack.size()-1; i>=0; i--) {
			result = result + "\n   called from line " + callStack.get(i);
		}
		return result;
	}

}
