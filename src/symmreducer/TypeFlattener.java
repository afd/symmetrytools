package src.symmreducer;

import java.util.ArrayList;
import java.util.List;


import src.etch.env.TypeEntry;
import src.etch.types.ArrayType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.Type;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;

public class TypeFlattener {

	public static List<VisibleType> flatten(Type t, StaticChannelDiagramExtractor typeInfo) {
		
		List<VisibleType> result = new ArrayList<VisibleType>();
		
		if(t instanceof RecordType) {
			TypeEntry typeEntry = (TypeEntry) typeInfo.getEnvEntry(t.name());
			for(String fieldName : typeEntry.getFieldNames()) {
				result.addAll(flatten(typeEntry.getFieldType(fieldName),typeInfo));
			}
		}
		
		else if(t instanceof ArrayType) {
			for(int i=0; i<((ArrayType)t).getLength(); i++) {
				result.addAll(flatten(((ArrayType)t).getElementType(),typeInfo));
			}
		}
		
		else if(t instanceof ProductType) {
			for(int i=0; i<((ProductType)t).getArity(); i++) {
				result.addAll(flatten(((ProductType)t).getTypeOfPosition(i),typeInfo));
			}
		}
		
		else {
			assert(t instanceof VisibleType);
			result.add((VisibleType) t);
		}
		
		return result;
		
	}
	
	
}
