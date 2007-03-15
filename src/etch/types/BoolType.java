package src.etch.types;

public class BoolType extends SimpleType {

	public String name() {
		return "bool";
	}

	public boolean isSubtype(Type t) {
		return equal(t);
	}

}
