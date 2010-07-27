package src.etch.types;


public class ByteType extends NumericType {
	
	public ByteType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public ByteType() {
		this(false);
	}

	public String name() {
		return "byte";
	}

	public boolean isSubtype(Type t) {
		return (t instanceof NumericType && !(t instanceof BitType)) || super.isSubtype(t);
	}

	@Override
	public String spinRepresentation() {
		return "uchar";
	}
	

}
