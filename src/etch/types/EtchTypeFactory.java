package src.etch.types;

import java.util.List;

public class EtchTypeFactory implements TypeFactory {

	public NumericType generateTypeForNumericLiteral(long val) {

		// The value is assumed to be in the range which SPIN
		// can accept. If it isn't, the value is untypable, and
		// should have already been rejected.
		
		if(val==0 || val==1) {
			return new BitType(true);
		}
		if(val<256 && val>1) {
			return new ByteType(true);
		}
		if(val<32768 && val>-32769) {
			return new ShortType(true);
		}
		return new IntType(true);
		
	}

	public BitType generateBitType() {
		return new BitType();
	}

	public ByteType generateByteType() {
		return new ByteType();
	}

	public ArrayType generateArrayType(VisibleType elementType,
			SimpleType indexType, int length) {
		return new ArrayType(elementType, indexType, length);
	}

	public ProductType generateProductType(List<Type> tuple) {
		return new ProductType(tuple);
	}

}
