package src.symmextractor.types;

import java.util.List;

import src.etch.types.SimpleType;
import src.etch.types.VisibleType;

public class PidType extends SimpleType implements VisibleType {
	
	public String name() {
		return "pid";
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

	@Override
	public String spinRepresentation() {
		return "uchar";
	}
	
	
}
