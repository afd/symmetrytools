package src.etch.typeinference;

import src.etch.types.Type;

/* Class to represent the constraint T <: U */

public class SubtypingConstraint extends Constraint {

	public SubtypingConstraint(Type lhs, Type rhs, int line) {
		super(lhs, rhs, line, "<:");
	}

}
