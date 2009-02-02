package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public class IncompatibleTypesError extends Error {

    private Type type1;
    private Type type2;

    public IncompatibleTypesError(Type t1, Type t2) {
		type1 = t1;
		type2 = t2;
    }

    public String message() {
    	return "\"" + Minimiser.minimise(type1).name() + "\" is not compatible with type \"" + Minimiser.minimise(type2).name() + "\" (mismatch found during type unification)";
    }
    
    @Override
	public void applySubstitutions(Substituter substituter) {
		type1 = substituter.applySubstitutions(type1);
		type2 = substituter.applySubstitutions(type2);
    }

}
