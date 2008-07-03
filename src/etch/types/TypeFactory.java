package src.etch.types;

import java.util.List;

public interface TypeFactory {

	public NumericType generateTypeForNumericLiteral(long val);
		
	public BitType generateBitType();

	public ByteType generateByteType();

	public ArrayType generateArrayType(VisibleType elementType, SimpleType indexType, int length);

	public ProductType generateProductType(List<Type> tuple);
	
}
