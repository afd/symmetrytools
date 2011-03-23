package src.symmextractor.types;

import java.util.List;

import src.etch.types.ArrayType;
import src.etch.types.BitType;
import src.etch.types.ByteType;
import src.etch.types.IntType;
import src.etch.types.NumericType;
import src.etch.types.ProductType;
import src.etch.types.ShortType;
import src.etch.types.SimpleType;
import src.etch.types.Type;
import src.etch.types.TypeFactory;
import src.etch.types.VisibleType;
import src.symmextractor.PidAwareChecker;

public class SymmExtractorTypeFactory implements TypeFactory {

	public NumericType generateTypeForNumericLiteral(long val) {

		if(val>=0 && val<=PidAwareChecker.numberOfRunningProcesses()) {

			if(val==0 || val==1) {
				return new PidSensitiveBitType(true,true);
			}
			if(val<256 && val>1) {
				return new PidSensitiveBitType(true,true);
			}
		}
		
		if(val==0 || val==1) {
			return new PidSensitiveBitType(true);
		}
		if(val<256 && val>1) {
			return new PidSensitiveByteType(true);
		}
		if(val<32768 && val>-32769) {
			return new ShortType(true);
		}
		return new IntType(true);
		
	}

	public BitType generateBitType() {
		return new PidSensitiveBitType();
	}

	public ByteType generateByteType() {
		return new PidSensitiveByteType();
	}

	public ArrayType generateArrayType(VisibleType elementType,
			SimpleType indexType, int length) {
		return new PidSensitiveArray(elementType, indexType, length);
	}

	public ProductType generateProductType(List<Type> tuple) {
		return new PidSensitiveProductType(tuple);
	}

}
