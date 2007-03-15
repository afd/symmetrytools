package src.etch.unifier;

import src.etch.types.Type;

/* Class to represent the constraint T = U */

public class EqualityConstraint extends Constraint {

	public EqualityConstraint(Type lhs, Type rhs, int line) {
		super(lhs, rhs, line, "=");
	}
}
