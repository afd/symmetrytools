package src.etch.types;

import junit.framework.Assert;

public class TypeVariableType extends SimpleType {

	private char letter;
	private int guid;
	private NumericType lower;
	private NumericType upper;

	protected TypeVariableType(char letter, int guid) {
		this.letter = letter;
		this.guid = guid;
		lower = null;
		upper = null;
	}

	public String name() {
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
