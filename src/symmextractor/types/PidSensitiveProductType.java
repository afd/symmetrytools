package src.symmextractor.types;

import java.util.List;

import src.etch.types.ChanType;
import src.etch.types.ProductType;
import src.etch.types.Type;
import src.etch.types.VisibleType;

public class PidSensitiveProductType extends ProductType {

	public PidSensitiveProductType(List<Type> tuple) {
		super(tuple);
	}

	public boolean hasInsensitiveField() {
		for(int i=0; i<getArity(); i++) {
			if (!(PidType.isPid((VisibleType) getTypeOfPosition(i)) || 
					ChanType.isChan((VisibleType) getTypeOfPosition(i)))) {
					return true;
			}
		}
		return false;
	}
	
}
