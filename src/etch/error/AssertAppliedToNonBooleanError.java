package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public class AssertAppliedToNonBooleanError extends Error {

	private Type type;
	
	public AssertAppliedToNonBooleanError(Type type) {
		this.type = type;
	}

	@Override
	public String message() {
		return "The assert operator can only be applied to a boolean expression, here it is applied to an expression with type \"" + Minimiser.minimise(type).name() + "\"";
	}
	
    @Override
	public void applySubstitutions(Substituter substituter) {
		type = substituter.applySubstitutions(type);
    }

}
