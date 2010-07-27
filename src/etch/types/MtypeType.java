package src.etch.types;

public class MtypeType extends SimpleType implements VisibleType {

	public String name() {
		return "mtype";
	}

	@Override
	public String spinRepresentation() {
		return "uchar";
	}

}
