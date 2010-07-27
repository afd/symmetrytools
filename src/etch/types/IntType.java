package src.etch.types;

public class IntType extends NumericType {

	public IntType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public IntType() {
		this(false);
	}

	public String name() {
		return "int";
	}

	public boolean isSubtype(Type t) {
		return equal(t) || super.isSubtype(t);
	}

	@Override
	public String spinRepresentation() {
		return name();
	}

}
