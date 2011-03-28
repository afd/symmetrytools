package src.symmreducer;

import java.util.ArrayList;
import java.util.List;

import src.etch.env.TypeEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.RecordType;
import src.etch.types.VisibleType;
import src.symmextractor.PidAwareChecker;
import src.symmextractor.types.PidType;

public class InsensitiveVariableReference extends VariableReference {

	public InsensitiveVariableReference(String reference, VisibleType type) {
		super(reference, type);
	}

	public static List<InsensitiveVariableReference> getInsensitiveVariableReferences(String varName, VisibleType varType, String prefix, PidAwareChecker typeInfo) {
		List<InsensitiveVariableReference> result = new ArrayList<InsensitiveVariableReference>();
		if (PidType.isPid(varType) || ChanType.isChan(varType) ||
				(ArrayType.isArray(varType) && PidType.isPid((VisibleType)((ArrayType)varType).getIndexType()))) {
			return result;
		}
		
		if (ArrayType.isArray(varType)) {
			for (int i = 0; i < ((ArrayType) varType).getLength(); i++) {
				result.addAll(getInsensitiveVariableReferences(varName + "[" + i
						+ "]", ((ArrayType) varType).getElementType(), prefix, typeInfo));
			}
			return result;
		}
		
		if (RecordType.isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) varType).name());
			for (String fieldName : typeEntry.getFieldNames()) {
				result.addAll(getInsensitiveVariableReferences(fieldName,
						typeEntry.getFieldType(fieldName), prefix + varName
								+ ".", typeInfo));
			}
			return result;
		}
		
		// Base case
		result.add(new InsensitiveVariableReference(prefix + varName,
				varType));

		return result;
	}
	
	
}
