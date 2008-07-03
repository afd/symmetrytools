package src.symmextractor.types;

import src.etch.types.ByteType;
import src.etch.types.Type;

public class PidSensitiveByteType extends ByteType implements PidLiteralCandidate {

	private boolean isPidLiteral;
	
	public PidSensitiveByteType(boolean isTypeOfConstant, boolean isPidLiteral) {
		super(isTypeOfConstant);
		this.isPidLiteral = isPidLiteral;
	}

	public PidSensitiveByteType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public PidSensitiveByteType() {
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
