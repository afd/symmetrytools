package src.symmreducer;

import src.etch.types.VisibleType;

class SensitiveVariableReference {

	private String reference;
	private VisibleType type;
	
	SensitiveVariableReference(String reference, VisibleType type) {
		this.reference = reference;
		this.type = type;
	}
	
	String getReference() {
		return reference;
	}
	
	VisibleType getType() {
		return type;
	}
	
}
