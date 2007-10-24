package src.etch.types;

import src.etch.checker.SymmetrySettings;

public abstract class NumericType extends SimpleType implements VisibleType {

	public static final long MAX_INT = 2147483647;
	public static final long MIN_INT = -2147483647;
	
	private boolean isTypeOfConstant;

	protected boolean isPidLiteral;

	public NumericType(boolean isTypeOfConstant, boolean isPidLiteral) {
		this.isTypeOfConstant = isTypeOfConstant;
		this.isPidLiteral = isPidLiteral;
	}

	public NumericType(boolean isTypeOfConstant) {
		this(isTypeOfConstant,false);
	}
	
	public boolean isTypeOfConstant() {
		return isTypeOfConstant;
	}

	public boolean isPidLiteral() {
		return isPidLiteral;
	}

	public void setNotPidLiteral() {
		isPidLiteral = false;
	}

	public void setIsTypeOfConstant() {
		isTypeOfConstant = true;
	}
	
	public static NumericType typeOfNumericLiteral(long val) {
		// The value is assumed to be in the range which SPIN
		// can accept. If it isn't, the value is untypable, and
		// should have already been rejected.

		if(SymmetrySettings.CHECKING_SYMMETRY) {

			if(val>=0 && val<=SymmetrySettings.noProcesses()) {

				if(val==0 || val==1) {
					return new BitType(true,true);
				}
				if(val<256 && val>1) {
					return new ByteType(true,true);
				}
			}
		}
		
		if(val==0 || val==1) {
			return new BitType(true);
		}
		if(val<256 && val>1) {
			return new ByteType(true);
		}
		if(val<32768 && val>-32769) {
			return new ShortType(true);
		}
		return new IntType(true);
		
	}

}
