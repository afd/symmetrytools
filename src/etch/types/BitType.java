package src.etch.types;


public class BitType extends NumericType {

	public BitType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public BitType() {
		this(false);
	}

	public String name() {
		return "bit";
	}

	public boolean isSubtype(Type t) {

		return t instanceof BoolType || t instanceof NumericType || super.isSubtype(t);

	}

	@Override
	public String spinRepresentation() {
		return "uchar";
	}

}
