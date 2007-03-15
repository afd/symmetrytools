package src.symmreducer;

import junit.framework.Assert;
import src.etch.types.ArrayType;

public class PidIndexedArrayReference extends SensitiveVariableReference {

	private ArrayType type;
	
	public PidIndexedArrayReference(String name, ArrayType type) {
		super(name,type);
		Assert.assertTrue(SymmetryApplier.isPid(type.getIndexType()));
		this.type = type;
	}

	public int getArrayLength() {
		return type.getLength();
	}
}
