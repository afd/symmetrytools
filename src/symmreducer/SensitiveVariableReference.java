package src.symmreducer;

import java.util.ArrayList;
import java.util.List;

import src.etch.env.TypeEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.RecordType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.types.PidType;

public class SensitiveVariableReference {

	private String reference;
	private VisibleType type;
	
	SensitiveVariableReference(String reference, VisibleType type) {
		this.reference = reference;
		this.type = type;
	}
		
	public VisibleType getType() {
		return type;
	}
	
	public String toString() {
		return reference;
	}

	public static List<SensitiveVariableReference> getSensitiveVariableReferences(String varName, VisibleType varType, String prefix, StaticChannelDiagramExtractor typeInfo) {
		List<SensitiveVariableReference> result = new ArrayList<SensitiveVariableReference>();
		if (PidType.isPid(varType) || ChanType.isChan(varType)) {
			result
					.add(new SensitiveVariableReference(prefix + varName,
							varType));
		} else if (ArrayType.isArray(varType)) {
			for (int i = 0; i < ((ArrayType) varType).getLength(); i++) {
				result.addAll(getSensitiveVariableReferences(varName + "[" + i
						+ "]", ((ArrayType) varType).getElementType(), prefix, typeInfo));
			}
		} else if (RecordType.isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) varType).name());
			for (String fieldName : typeEntry.getFieldNames()) {
				result.addAll(getSensitiveVariableReferences(fieldName,
						typeEntry.getFieldType(fieldName), prefix + varName
								+ ".", typeInfo));
			}
		}

		return result;
	}

	public static List<String> getInsensitiveVariableReferences(String varName,
			VisibleType varType, StaticChannelDiagramExtractor typeInfo) {
		return getInsensitiveVariableReferences(varName, varType, typeInfo, "");
	}
	
	
	private static List<String> getInsensitiveVariableReferences(String varName,
			VisibleType varType, StaticChannelDiagramExtractor typeInfo, String prefix) {
		List<String> result = new ArrayList<String>();

		if (PidType.isPid(varType) || ChanType.isChan(varType)) {
			return result;
		}

		if (ArrayType.isArray(varType)) {
			assert(((ArrayType) varType).getIndexType() instanceof VisibleType);
			if (PidType.isPid((VisibleType) ((ArrayType) varType).getIndexType())) {
				return result;
			}

			for (int i = 0; i < ((ArrayType) varType).getLength(); i++) {
				result.addAll(getInsensitiveVariableReferences(varName + "["
						+ i + "]", ((ArrayType) varType).getElementType(),
						typeInfo, prefix));
				return result;
			}
		}

		if (RecordType.isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) varType).name());
			for (String fieldName : typeEntry.getFieldNames()) {
				result.addAll(getInsensitiveVariableReferences(fieldName,
						typeEntry.getFieldType(fieldName), typeInfo, prefix + varName
						+ "."));
			}
			return result;
		}

		result.add(prefix + varName);
		return result;

	}
	
	
}
