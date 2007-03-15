package src.etch.types;

public class ArrayType extends Type {

	private Type elementType;
	private SimpleType indexType;
	private int length;
	
	public ArrayType(Type elementType, SimpleType indexType, int length) {
		this.elementType = elementType;
		this.indexType = indexType;
		this.length = length;
	}

	public Type getElementType() {
		return elementType;
	}

	public SimpleType getIndexType() {
		return indexType;
	}
	
	public int getLength() {
		return length;
	}

	public boolean isSubtype(Type t) {
		return (t.equal(this));
	}

	protected void setElementType(Type t) {
		elementType = t;
	}

	protected void setIndexType(SimpleType t) {
		indexType = t;
	}

	public void zeroLength() {
		length = 0;
	}

}
