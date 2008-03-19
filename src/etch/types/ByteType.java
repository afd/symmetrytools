package src.etch.types;

import src.etch.checker.SymmetrySettings;

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
		return (!SymmetrySettings.CHECKING_SYMMETRY && t instanceof PidType) ||
			(SymmetrySettings.CHECKING_SYMMETRY && t instanceof PidType && isPidLiteral) || t instanceof ByteType || t instanceof ShortType || t instanceof IntType;
	}

	public static boolean isByte(VisibleType type) {
		return type instanceof ByteType;
	}
	
}
