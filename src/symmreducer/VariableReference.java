package src.symmreducer;

import src.etch.types.VisibleType;

public class VariableReference {

	protected String reference;
	protected VisibleType type;
	
	VariableReference(String reference, VisibleType type) {
		this.reference = reference;
		this.type = type;
	}

	public VisibleType getType() {
		return type;
	}
	
	public String toString() {
		return reference;
	}
	
}
