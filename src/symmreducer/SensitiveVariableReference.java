package src.symmreducer;

import src.etch.types.Type;

class SensitiveVariableReference {

	private String reference;
	private Type type;
	
	SensitiveVariableReference(String reference, Type type) {
		this.reference = reference;
		this.type = type;
	}
	
	String getReference() {
		return reference;
	}
	
	Type getType() {
		return type;
	}
	
}
