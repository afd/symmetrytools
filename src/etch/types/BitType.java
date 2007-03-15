package src.etch.types;

public class BitType extends NumericType {

	public BitType(boolean isTypeOfConstant, boolean isPidLiteral) {
		super(isTypeOfConstant);
		this.isPidLiteral = isPidLiteral;
	}

	public BitType(boolean isTypeOfConstant) {
		this(isTypeOfConstant,false);
	}

	public BitType() {
		this(false,false);
	}

	public String name() {
		return "bit";
	}

	public boolean isSubtype(Type t) {
		return (!checkingSymmetry() && t instanceof PidType) ||
		(checkingSymmetry() && t instanceof PidType && isPidLiteral) || t instanceof BoolType || t instanceof NumericType;
	}

}
