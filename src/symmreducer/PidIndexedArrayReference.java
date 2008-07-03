package src.symmreducer;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import src.etch.env.TypeEntry;
import src.etch.types.ArrayType;
import src.etch.types.ByteType;
import src.etch.types.RecordType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.types.PidType;

public class PidIndexedArrayReference extends SensitiveVariableReference {

	private ArrayType type;
	
	public PidIndexedArrayReference(String name, ArrayType type) {
		super(name,type);
		Assert.assertTrue(type.getIndexType() instanceof VisibleType);
		Assert.assertTrue(PidType.isPid((VisibleType) type.getIndexType()));
		this.type = type;
	}

	public int getArrayLength() {
		return type.getLength();
	}
	
	public static List<PidIndexedArrayReference> getSensitivelyIndexedArrayReferences(
			String name, VisibleType type, String referencePrefix, StaticChannelDiagramExtractor typeInfo) {

		List<PidIndexedArrayReference> result = new ArrayList<PidIndexedArrayReference>();
		if (ArrayType.isArray(type)) {
			if (PidType.isPid((VisibleType) ((ArrayType) type).getIndexType())
					&& !ByteType.isByte((VisibleType) ((ArrayType) type).getIndexType())) {
				result.add(new PidIndexedArrayReference(referencePrefix + name,
						(ArrayType) type));
			}
			for (int i = 0; i < ((ArrayType) type).getLength(); i++) {
				result.addAll(getSensitivelyIndexedArrayReferences(name + "["
						+ i + "]", ((ArrayType) type).getElementType(),
						referencePrefix, typeInfo));
			}
		} else if (RecordType.isRecord(type)) {
			TypeEntry recordEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) type).name());
			for (String fieldName : recordEntry.getFieldNames()) {
				result.addAll(getSensitivelyIndexedArrayReferences(fieldName,
						recordEntry.getFieldType(fieldName), referencePrefix
								+ name + ".", typeInfo));
			}
		}

		return result;
	}
	
}
