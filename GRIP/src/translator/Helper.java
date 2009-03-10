package src.translator;

import java.util.ArrayList;
import java.util.List;

import src.symmetricprism.node.AListRangePrefix;
import src.symmetricprism.node.ARange;
import src.symmetricprism.node.ASequenceRangePrefix;
import src.symmetricprism.node.TName;

public class Helper {

	protected static int toInt(String text) {
		return Integer.parseInt(text);
	}

	protected static int determineDigitIndex(TName identifier) {
		for(int i=0; i<identifier.getText().length(); i++) {
			if(Character.isDigit(identifier.getText().charAt(i))) {
				return i;
			}
		}
		
		// When there is no digit, return the length of the identifier
		return identifier.getText().length();
	}

	protected static String extractName(TName identifier) {
		return identifier.getText().substring(0,determineDigitIndex(identifier));
	}

	protected static int extractNumber(TName identifier) {
		// Return 0 if there is no number
		if(determineDigitIndex(identifier)==identifier.getText().length()) {
			return 0;
		}
		return Integer.parseInt(identifier.getText().substring(determineDigitIndex(identifier)));
	}

	protected static List<Integer> extractRange(ARange range) {
		List<Integer> result = new ArrayList<Integer>();
		int startOfRange = -1;
		
		for(Object o : range.getRangePrefix()) {
			if(o instanceof ASequenceRangePrefix) {
				if(startOfRange != -1) {
					for(int i=startOfRange; i<toInt(((ASequenceRangePrefix)o).getNumber().getText()); i++) {
						result.add(i);
					}
					startOfRange = -1;
				}
				result.add(toInt(((ASequenceRangePrefix)o).getNumber().getText()));
			} else {
				if(startOfRange!=-1) {
					System.out.println("Badly formed range " + range + " at line " + ((AListRangePrefix)o).getNumber().getLine());
					System.exit(0);
				}
				startOfRange = toInt(((AListRangePrefix)o).getNumber().getText());
			}
		}

		if(startOfRange != -1) {
			for(int i=startOfRange; i<toInt(range.getNumber().getText()); i++) {
				result.add(i);
			}
			startOfRange = -1;
		}

		result.add(toInt(range.getNumber().getText()));
		return result;
	}
    
}