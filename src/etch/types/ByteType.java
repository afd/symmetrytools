package src.etch.types;

public class ByteType extends NumericType {
	
	public ByteType(boolean isTypeOfConstant, boolean isPidLiteral) {
		super(isTypeOfConstant);
		this.isPidLiteral = isPidLiteral;
	}

	public ByteType(boolean isTypeOfConstant) {
		this(isTypeOfConstant,false);
	}

	public ByteType() {
		this(false,false);
	}

	public String name() {
		return "byte";
	}

	public boolean isSubtype(Type t) {
		return (!checkingSymmetry() && t instanceof PidType) ||
			(checkingSymmetry() && t instanceof PidType && isPidLiteral) || t instanceof ByteType || t instanceof ShortType || t instanceof IntType;
	}
	
}
