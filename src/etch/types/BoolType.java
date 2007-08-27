package src.etch.types;

public class BoolType extends SimpleType implements VisibleType {

	public String name() {
		return "bool";
	}

	public boolean isSubtype(Type t) {
		return equal(t);
	}

}
