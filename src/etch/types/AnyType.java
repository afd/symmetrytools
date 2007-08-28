package src.etch.types;

import src.etch.error.IncomparableTypesException;

public abstract class AnyType implements Type {

	public String toString() {
		return name();
	}

	public static Type max(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t2;
		} else if (t2.isSubtype(t1)) {
			return t1;
		}
		/* Throw an exception if the types are incomparable */
		throw new IncomparableTypesException(t1,t2);
	}

	public static Type min(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t1;
		} else if (t2.isSubtype(t1)) {
			return t2;
		}
		/* Throw an exception if the types are incomparable */
		throw new IncomparableTypesException(t1,t2);
	}
		
}
