package src.etch.types;

public abstract class SimpleType extends Type {

	public abstract String name();

	public abstract boolean isSubtype(Type t);

	public final boolean equal(Type t) {
		return t instanceof SimpleType && name().equals(t.name());
	}
}
