package src.etch.types;

public class RecordType extends SimpleType implements VisibleType {

	private String name;

	public RecordType(String name) {
		this.name = name;
	}
	
	public String name() {
		return name;
	}

	public static boolean isRecord(VisibleType t) {
		return t instanceof RecordType;
	}

	@Override
	public String spinRepresentation() {
		return "struct " + name();
	}

	
}
