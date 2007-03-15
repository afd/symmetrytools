package src.etch.unifier;

import src.etch.types.Type;

public abstract class Constraint {

	private Type lhs;
	
	private Type rhs;

	private int line;

	private String operator;
	
	protected Constraint(Type lhs, Type rhs, int line, String operator) {
		this.lhs = lhs;
		this.rhs = rhs;
		this.line = line;
		this.operator = operator;
	}

	public Type getLhs() {
		return lhs;
	}

	public Type getRhs() {
		return rhs;
	}

	public int getLine() {
		return line;
	}
	
	public String toString() {
		return lhs.name() + " " + operator + " " + rhs.name();
	}

}
