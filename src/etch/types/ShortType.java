package src.etch.types;

public class ShortType extends NumericType {

	public ShortType(boolean isTypeOfConstant) {
		super(isTypeOfConstant);
	}

	public ShortType() {
		this(false);
	}

	public String name() {
		return "short";
	}

	public boolean isSubtype(Type t) {
		return super.isSubtype(t) || t instanceof ShortType || t instanceof IntType;
	}

}
