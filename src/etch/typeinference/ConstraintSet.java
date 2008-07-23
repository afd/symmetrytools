package src.etch.typeinference;

import java.util.ArrayList;
import java.util.List;

import src.etch.error.Error;
import src.etch.error.ErrorTable;

public class ConstraintSet {

	private List<EqualityConstraint> equalityConstraints;
	private List<SubtypingConstraint> subtypingConstraints;
	private Unifier unifier;
	
	public ConstraintSet(Unifier unifier) {
		equalityConstraints = new ArrayList<EqualityConstraint>();
		subtypingConstraints = new ArrayList<SubtypingConstraint>();
		this.unifier = unifier;
	}

	public void add(Constraint c) {
		if(c instanceof EqualityConstraint) {
			equalityConstraints.add((EqualityConstraint)c);
		} else {
			subtypingConstraints.add((SubtypingConstraint)c);
		}
	}
	
	public Substituter unify(ErrorTable et) {
		
		for (SubtypingConstraint c : subtypingConstraints) {

			Error e = unifier.unifySubtypingConstraint(c, equalityConstraints);
			if (e != null) {
				et.add(c.getLine(), e);
			}
		}

		for (EqualityConstraint c : equalityConstraints) {
			
			Error e = unifier.unifyConstraint(c.getLhs(),c.getRhs());
			if (e != null) {
				et.add(c.getLine(), e);
			}
		}

		return new Substituter(unifier);

	}
	
}
