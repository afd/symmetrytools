package src.etch.types;

public class MtypeType extends SimpleType {

	public String name() {
		return "mtype";
	}

	public boolean isSubtype(Type t) {
		return equal(t);
	}

}
