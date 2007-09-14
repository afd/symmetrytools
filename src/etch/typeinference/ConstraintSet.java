package src.etch.typeinference;

import java.util.ArrayList;
import java.util.List;

import src.etch.error.Error;
import src.etch.error.ErrorTable;

public class ConstraintSet {

	private List<EqualityConstraint> equalityConstraints;
	private List<SubtypingConstraint> subtypingConstraints;

	public ConstraintSet() {
		equalityConstraints = new ArrayList<EqualityConstraint>();
		subtypingConstraints = new ArrayList<SubtypingConstraint>();
	}

	public void add(Constraint c) {
		if(c instanceof EqualityConstraint) {
			equalityConstraints.add((EqualityConstraint)c);
		} else {
			subtypingConstraints.add((SubtypingConstraint)c);
		}
	}
	
	public Substituter unify(ErrorTable et) {

		Unifier graph = new Unifier();
		
		for (SubtypingConstraint c : subtypingConstraints) {

			Error e = graph.unifySubtypingConstraint(c, equalityConstraints);
			if (e != null) {
				et.add(c.getLine(), e);
			}
		}

		for (EqualityConstraint c : equalityConstraints) {
			
			Error e = graph.unifyConstraint(c.getLhs(),c.getRhs());
			if (e != null) {
				et.add(c.getLine(), e);
			}
		}

		return new Substituter(graph);

	}
	
}
