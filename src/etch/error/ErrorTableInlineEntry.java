package src.etch.error;

import java.util.ArrayList;
import java.util.List;

import src.utilities.Config;

public class ErrorTableInlineEntry extends ErrorTableEntry {

	private List<Integer> callStackLineNumbers;
	private List<String> callStackNames;
	
	public ErrorTableInlineEntry(int line, List<Integer> callStackLineNumbers, List<String> callStackNames, Error e) {
		super(line,e);
		this.callStackLineNumbers = new ArrayList<Integer>(callStackLineNumbers);
		this.callStackNames = new ArrayList<String>(callStackNames);
	}

	@Override
	public String output(String sourceName) {
		String result = super.output(sourceName);
		for(int i=callStackLineNumbers.size()-1; i>=0; i--) {
			result += "\n   called from ";
			if(i>0) {
				result += "\"" + callStackNames.get(i-1) + "\"";
			} else {
				result += "main specification";
			}
			result += " at ";
			
			String file;
			int actualLine;
			
			if(null == Config.locations.get(callStackLineNumbers.get(i)))
			{
				file = "\"" + sourceName + "\"";
				actualLine = callStackLineNumbers.get(i);
			} else {
				file = Config.locations.get(callStackLineNumbers.get(i)).getFile();
				actualLine = Config.locations.get(callStackLineNumbers.get(i)).getLine();
			}
			
			result += file + ", line " + actualLine;
		}
		return result;
	}

}
