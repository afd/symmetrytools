package src.etch.types;

public class BoolType extends SimpleType implements VisibleType {

	public String name() {
		return "bool";
	}

	@Override
	public String spinRepresentation() {
		return "uchar";
	}

}
