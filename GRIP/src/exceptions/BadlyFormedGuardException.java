package src.exceptions;

import src.symmetricprism.node.Node;

@SuppressWarnings("serial")
public class BadlyFormedGuardException extends Exception {

	private Node expr;
	private int line;
	
	public BadlyFormedGuardException(Node expr, int line) {
		this.expr = expr;
	}

	public String toString() {
		return "Error at line " + line + ": Guard \"" + expr + "\" is badly formed.";
	}
	
}
