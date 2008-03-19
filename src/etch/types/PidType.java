package src.etch.types;

import java.util.List;

import src.etch.checker.SymmetrySettings;

public class PidType extends SimpleType implements VisibleType {

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

	public static boolean isPid(VisibleType t) {
		return t instanceof PidType;
	}

	public static boolean containsPidType(List<VisibleType> typeList) {
		for (VisibleType vt : typeList) {
			if (isPid(vt)) {
				return true;
			}
		}
		return false;
	}

	public static int getNumberOfPidTypes(List<VisibleType> typeList) {
		int result = 0;
		for(VisibleType vt : typeList) {
			if(isPid(vt)) {
				result++;
			}
		}
		return result;
	}
	
	
}
