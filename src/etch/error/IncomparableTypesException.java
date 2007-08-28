package src.etch.error;

import src.etch.types.Type;

@SuppressWarnings("serial")
public class IncomparableTypesException extends Exception {

	private Type left;

	private Type right;

	public IncomparableTypesException(Type left, Type right) {
		this.left = left;
		this.right = right;
	}

	public Type getLeftType() {
		return left;
	}

	public Type getRightType() {
		return right;
	}

	public String toString() {
		return "Error: attempted to compare types " + left + " and " + right
				+ ", which are not subtypes of one another.";
	}

}
