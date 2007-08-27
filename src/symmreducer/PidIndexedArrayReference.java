package src.symmreducer;

import junit.framework.Assert;
import src.etch.types.ArrayType;
import src.etch.types.VisibleType;

public class PidIndexedArrayReference extends SensitiveVariableReference {

	private ArrayType type;
	
	public PidIndexedArrayReference(String name, ArrayType type) {
		super(name,type);
		Assert.assertTrue(type.getIndexType() instanceof VisibleType);
		Assert.assertTrue(SymmetryApplier.isPid((VisibleType) type.getIndexType()));
		this.type = type;
	}

	public int getArrayLength() {
		return type.getLength();
	}
}
