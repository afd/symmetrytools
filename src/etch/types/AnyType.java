package src.etch.types;

import java.util.ArrayList;
import java.util.List;



import src.etch.checker.Checker;
import src.etch.error.IncomparableTypesException;

public abstract class AnyType implements Type {

	public static Type max(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t2;
		} else if (t2.isSubtype(t1)) {
			return t1;
		}
		/* Throw an exception if the types are incomparable */
		throw new IncomparableTypesException(t1,t2);
	}

	public static Type uncheckedMax(Type t1, Type t2) {
		assert(t1.isSubtype(t2) || t2.isSubtype(t1));
		if(t1.isSubtype(t2)) {
			return t2;
		}
		return t1;
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

	public static Type uncheckedMin(Type t1, Type t2) {
		assert(t1.isSubtype(t2) || t2.isSubtype(t1));
		if(t1.isSubtype(t2)) {
			return t1;
		}
		return t2;
	}
	
	public String name() {
		List<String> nameComponents = new ArrayList<String>();
		nameComponentsDFS(new TypeStack(this),nameComponents);
		String result = "";
		for(String component : nameComponents) {
			result += component;
		}
		return result;
	}

	public abstract void nameComponentsDFS(TypeStack stack, List<String> result);

	public static void resetTypeFactory() {
		Checker.theFactory = null;
	}
	
	public boolean isSubtype(Type t) {
		return equal(t) || t instanceof TopType;
	}
	
}
