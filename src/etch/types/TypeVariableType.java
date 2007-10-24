package src.etch.types;

import junit.framework.Assert;

public class TypeVariableType extends SimpleType implements InternalType {

	private static char prettyVariables[] = { 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z' };
	
	private char letter;
	private int guid;
	private NumericType lower;
	private NumericType upper;
	private boolean prettyPrint;
	
	protected TypeVariableType(char letter, int guid, boolean prettyPrint) {
		this.letter = letter;
		this.guid = guid;
		this.prettyPrint = prettyPrint;
		lower = null;
		upper = null;
	}

	public String name() {
		if(prettyPrint && guid < prettyVariables.length) {
			return "" + prettyVariables[guid];
		}
		return String.valueOf(letter) + guid;
	}

	public void setLower(NumericType lower) {
		this.lower = lower;
	}

	public void setUpper(NumericType upper) {
		this.upper = upper;
	}

	public NumericType getLower() {
		return lower;
	}

	public NumericType getUpper() {
		return upper;
	}

	public boolean isSubtype(Type t) {
		Assert.assertTrue(false);
		return false;
	}

}
