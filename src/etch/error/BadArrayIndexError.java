package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.NumericType;
import src.etch.types.Type;

public class BadArrayIndexError extends Error {

	private Type actualType;
	private NumericType expectedType;
	
	public BadArrayIndexError(Type actualType, NumericType expectedType) {
		this.actualType = actualType;
		this.expectedType = expectedType;
	}

	@Override
	public String message() {
		return "Type \"" + Minimiser.minimise(actualType).name() + "\" cannot be used as an array index, it is not a subtype of \"" + expectedType.name() + "\"";
	}
	
    @Override
	public void applySubstitutions(Substituter substituter) {
		actualType = substituter.applySubstitutions(actualType);
		// No need to substitute expectedType, as it is ByteType
    }
	

}
