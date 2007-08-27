package src.etch.types;

public abstract class SimpleType extends AnyType {

	public final boolean equal(Type t) {
		return t instanceof SimpleType && name().equals(t.name());
	}
}
