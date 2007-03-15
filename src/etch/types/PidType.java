package src.etch.types;

public class PidType extends SimpleType {

	public String name() {
		if(checkingSymmetry()) {
			return "pid";
		}
		return "byte";
	}

	public boolean isSubtype(Type t) {
		if(checkingSymmetry()) {
			return equal(t);
		}
		
		return new ByteType().isSubtype(t);
	}

}
