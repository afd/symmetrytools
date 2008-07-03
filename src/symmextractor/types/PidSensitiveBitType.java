package src.symmextractor.types;

import src.etch.types.BitType;
import src.etch.types.Type;

public class PidSensitiveBitType extends BitType implements PidLiteralCandidate {

	private boolean isPidLiteral;
	
	public PidSensitiveBitType(boolean isTypeOfConstant, boolean isPidLiteral) {
		super(isTypeOfConstant);
		this.isPidLiteral = isPidLiteral;
	}

	public PidSensitiveBitType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public PidSensitiveBitType() {
		super();
	}

	@Override
	public boolean isSubtype(Type t) {
		return (t instanceof PidType && isPidLiteral) || super.isSubtype(t);
	}

	public void setNotPidLiteral() {
		isPidLiteral = false;
	}

	public boolean isPidLiteral() {
		return isPidLiteral;
	}

}
