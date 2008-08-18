package src.etch.types;



public class TopType extends SimpleType {

	private int numberConstructed = 0;

	public static final TopType uniqueInstance = new TopType();

	private TopType() {
		assert(numberConstructed == 0);
		numberConstructed++;
	}
	
	public String name() {
		return "top";
	}

	public boolean isSubtype(Type t) {
		return t instanceof TopType;
	}

}
