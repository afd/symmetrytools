package src.etch.types;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import junit.framework.Assert;

public class ArrayType extends ConstructedType implements VisibleType {

	private VisibleType elementType;
	private SimpleType indexType;
	private int length;
	
	public ArrayType(VisibleType elementType, SimpleType indexType, int length) {
		Assert.assertTrue(indexType instanceof ByteType || indexType instanceof PidType || indexType instanceof TypeVariableType);
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
		String result = "";
		if(elementType instanceof SimpleType) {
			result += elementType.name();
		} else {
			result += ((ConstructedType)elementType).nameRecursive(factory);
		}
		return result + "[" + this.indexType.name() + "]";
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

	protected ConstructedType cloneAndUnrollPlugin(Map<ConstructedType, ConstructedType> cloneMap) {

		if(elementType instanceof SimpleType) {
			return new ArrayType(elementType,indexType,length);
		}

		Assert.assertTrue(elementType instanceof ConstructedType);

		ArrayType clonedArray = new ArrayType(null,indexType,length);

		cloneMap.put(this,clonedArray);
		
		clonedArray.setElementType((VisibleType) ((ConstructedType)elementType).cloneAndUnroll(cloneMap));

		return clonedArray;
			
	}

	
}
