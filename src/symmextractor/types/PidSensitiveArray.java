package src.symmextractor.types;

import src.etch.types.ArrayType;
import src.etch.types.SimpleType;
import src.etch.types.TypeVariableType;
import src.etch.types.VisibleType;

public class PidSensitiveArray extends ArrayType {

	public PidSensitiveArray(VisibleType elementType, SimpleType indexType,
			int length) {
		super(elementType, indexType, length);
	}

	protected String indexToString() {
		String result = "size " + length;

		if(!(this.indexType instanceof TypeVariableType)) {
			result += ", indexed by " + this.indexType.name();
		}

		return result;

	}

}
