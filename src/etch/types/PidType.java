package src.etch.types;

import src.etch.checker.SymmetrySettings;

public class PidType extends SimpleType {

	public String name() {
		if(SymmetrySettings.CHECKING_SYMMETRY) {
			return "pid";
		}
		return "byte";
	}

	public boolean isSubtype(Type t) {
		if(SymmetrySettings.CHECKING_SYMMETRY) {
			return equal(t);
		}
		
		return new ByteType().isSubtype(t);
	}

}
