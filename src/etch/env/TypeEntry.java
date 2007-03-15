package src.etch.env;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import junit.framework.Assert;
import src.etch.types.Type;

public class TypeEntry extends EnvEntry {

	private List<String> fieldNames;
	private List<Type> fieldTypes;
	
	public TypeEntry(List<String> fieldNames, List<Type> fieldTypes) {
		Assert.assertEquals(fieldNames.size(),fieldTypes.size());
		this.fieldNames = new ArrayList<String>();
		this.fieldTypes = new ArrayList<Type>();
		for(int i=0; i<fieldNames.size(); i++) {
			this.fieldNames.add(fieldNames.get(i));
			this.fieldTypes.add(fieldTypes.get(i));
		}
	}

	public Type getFieldType(String fieldName) {
		Assert.assertTrue(fieldNames.contains(fieldName));
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
}
