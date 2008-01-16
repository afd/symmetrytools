package src.etch.types;

import java.util.HashSet;
import java.util.Set;

import junit.framework.Assert;
import src.etch.checker.SymmetrySettings;

public class ArrayType extends ConstructedType implements VisibleType {

	private VisibleType elementType;
	private SimpleType indexType;
	private int length;
	
	public ArrayType(VisibleType elementType, SimpleType indexType, int length) {
		Assert.assertTrue(indexType==null || indexType instanceof ByteType || indexType instanceof PidType || indexType instanceof TypeVariableType);
		this.elementType = elementType;
		this.indexType = indexType;
		this.length = length;
	}

	public VisibleType getElementType() {
		return elementType;
	}

	public SimpleType getIndexType() {
		return indexType;
	}
	
	public int getLength() {
		return length;
	}

	public void setElementType(VisibleType t) {
		/* Unfortunately this needs to be public, as it
		 * is called by the Substituter class which is in
		 * a different package (as it really should be) 
		*/
		elementType = t;
	}

	public void setIndexType(SimpleType t) {
		indexType = t;
	}

	public void zeroLength() {
		length = 0;
	}

	protected String namePlugin(TypeVariableFactory factory) {
		String result = "array (size " + length;

		if(SymmetrySettings.CHECKING_SYMMETRY && !(this.indexType instanceof TypeVariableType)) {
			result += ", indexed by " + this.indexType.name();
		}

		result += ") of ";
		
		if(elementType instanceof SimpleType) {
			result += elementType.name();
		} else {
			result += ((ConstructedType)elementType).nameRecursive(factory);
		}

		return result;
	}

	protected void replaceChildWithTypeVariable(ConstructedType type, TypeVariableType tVar) {
		Assert.assertTrue(false);
	}

	protected Set<ConstructedType> computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(ConstructedType type, Set<ConstructedType> alreadyVisited) {
		Set<ConstructedType> result = new HashSet<ConstructedType>();
		if(alreadyVisited.contains(this)) {
			// We've already checked this node
			return result;
		}
		
		// Mark this node as checked
		alreadyVisited.add(this);

		if(elementType instanceof ConstructedType) {
			if(elementType == type) {
				result.add(this);
			} else {
				result.addAll(((ConstructedType)elementType).computeDescendentsOfTypeWhichAreAlsoDirectPredecessors((ConstructedType) type,alreadyVisited));
			}
		}
		
		return result;
	}
	
}
