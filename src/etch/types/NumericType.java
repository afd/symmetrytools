package src.etch.types;


public abstract class NumericType extends SimpleType implements VisibleType {

	public static final long MAX_INT = 2147483647;
	public static final long MIN_INT = -2147483647;
	
	private boolean isTypeOfConstant;

	public NumericType(boolean isTypeOfConstant) {
		this.isTypeOfConstant = isTypeOfConstant;
	}
	
	public boolean isTypeOfConstant() {
		return isTypeOfConstant;
	}

	public void setIsTypeOfConstant() {
		isTypeOfConstant = true;
	}	

}
