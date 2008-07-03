package src.etch.types;

import junit.framework.Assert;

public final class BottomType extends SimpleType implements VisibleType {

	private int numberConstructed = 0;

	public static final BottomType uniqueInstance = new BottomType();

	private BottomType() {
		Assert.assertEquals(numberConstructed,0);
		numberConstructed++;
	}
	
	public String name() {
		return "bottom";
	}

	public boolean isSubtype(Type t) {
		return true;
	}

}
