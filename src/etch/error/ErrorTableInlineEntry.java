package src.etch.error;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

public class ErrorTableInlineEntry extends ErrorTableEntry {

	private List<Integer> callStackLineNumbers;
	private List<String> callStackNames;
	
	public ErrorTableInlineEntry(int line, List<Integer> callStackLineNumbers, List<String> callStackNames, Error e) {
		super(line,e);
		this.callStackLineNumbers = new ArrayList<Integer>(callStackLineNumbers);
		this.callStackNames = new ArrayList<String>(callStackNames);
	}
	
	public void output(PrintStream out) {
		out.print(output());
	}

	public String output() {
		String result = super.output();
		for(int i=callStackLineNumbers.size()-1; i>=0; i--) {
			result += "\n   called from ";
			if(i>0) {
				result += "\"" + callStackNames.get(i-1) + "\"";
			} else {
				result += "main specification";
			}
			result += " at line " + callStackLineNumbers.get(i);
		}
		return result;
	}

}
