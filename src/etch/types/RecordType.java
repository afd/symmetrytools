package src.etch.types;

public class RecordType extends SimpleType implements VisibleType {

	private String name;

	public RecordType(String name) {
		this.name = name;
	}
	
	public String name() {
		return name;
	}

	public boolean isSubtype(Type t) {
		return equal(t);
	}

	
}
