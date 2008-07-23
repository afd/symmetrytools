package src.etch.types;



public abstract class ConstructedType extends AnyType {

	public boolean equal(Type t) {
		return t instanceof ConstructedType &&
		 ((ConstructedType)t).minimisedName().equals(this.minimisedName());
	}

	private String minimisedName() {
		return Minimiser.minimise(this).name();
	}

	public final String name() {
		return super.name();
	}
	
}
