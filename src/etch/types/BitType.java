package src.etch.types;

import src.etch.checker.SymmetrySettings;

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
		return (!SymmetrySettings.CHECKING_SYMMETRY && t instanceof PidType) ||
		(SymmetrySettings.CHECKING_SYMMETRY && t instanceof PidType && isPidLiteral) || t instanceof BoolType || t instanceof NumericType;
	}

}
