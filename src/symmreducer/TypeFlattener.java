package src.symmreducer;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import src.etch.env.TypeEntry;
import src.etch.types.ArrayType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.Type;
import src.symmextractor.StaticChannelDiagramExtractor;

public class TypeFlattener {

	public static List<Type> flatten(Type t, StaticChannelDiagramExtractor typeInfo) {
		
		List<Type> result = new ArrayList<Type>();
		
		if(t instanceof RecordType) {
			TypeEntry typeEntry = (TypeEntry) typeInfo.getEnvEntry(t.name());
			for(Iterator<String> itr = typeEntry.getFieldNames().iterator(); itr.hasNext();) {
				result.addAll(flatten(typeEntry.getFieldType(itr.next()),typeInfo));
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
			result.add(t);
		}
		
		return result;
		
	}
	
	
}
