package src.etch.types;

import java.util.List;

public class ArrayType extends ConstructedType implements VisibleType {

	protected VisibleType elementType;
	protected SimpleType indexType;
	protected int length;
	
	public ArrayType(VisibleType elementType, SimpleType indexType, int length) {
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
	
	public static boolean isArray(VisibleType t) {
		return t instanceof ArrayType;
	}
	
	public void nameComponentsDFS(TypeStack stack, List<String> result) {

		String component = "array(" + indexToString() + ") of ";

		result.add(component);

		if(stack.push(elementType,result)) {
			elementType.nameComponentsDFS(stack,result);
			stack.pop();
		}

	}

	protected String indexToString() {
		return "size " + length;
	}

	@Override
	public String spinRepresentation() {
		// We cannot directly output the SPIN representation for an array,
		// since C array types are tangled up with variable names.
		assert(false);
		return null;
	}
	
}
