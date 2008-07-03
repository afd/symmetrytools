package src.etch.types;

import junit.framework.Assert;

public class TopType extends SimpleType {

	private int numberConstructed = 0;

	public static final TopType uniqueInstance = new TopType();

	private TopType() {
		Assert.assertEquals(numberConstructed,0);
		numberConstructed++;
	}
	
	public String name() {
		return "top";
	}

	public boolean isSubtype(Type t) {
		return t instanceof TopType;
	}

}
