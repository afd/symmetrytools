package src.etch.env;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


import src.etch.types.VisibleType;

public class TypeEntry extends EnvEntry {

	private List<String> fieldNames;
	private List<VisibleType> fieldTypes;
	
	public TypeEntry(List<String> fieldNames, List<VisibleType> fieldTypes, int lineOfDeclaration) {
		super(lineOfDeclaration);
		assert(fieldNames.size() == fieldTypes.size());
		this.fieldNames = new ArrayList<String>();
		this.fieldTypes = new ArrayList<VisibleType>();
		for(int i=0; i<fieldNames.size(); i++) {
			this.fieldNames.add(fieldNames.get(i));
			this.fieldTypes.add(fieldTypes.get(i));
		}
	}

	public VisibleType getFieldType(String fieldName) {
		if(!fieldNames.contains(fieldName)) {
			return null;
		}
		return fieldTypes.get(fieldNames.indexOf(fieldName));
	}

	public List<String> getFieldNames() {
		return Collections.unmodifiableList(fieldNames);
	}

	public String toString() {
		String result = "{ ";
		for(int i=0; i<fieldNames.size(); i++) {
			result = result + getFieldType(fieldNames.get(i)).name() + " " + fieldNames.get(i);
			if(i<fieldNames.size()-1) {
				result = result + "; ";
			}
		}
		return result + " }";
	}

	public String getEntryKind() {
		return "typedef";
	}

}
