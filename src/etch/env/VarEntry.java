package src.etch.env;

import src.etch.types.VisibleType;

public class VarEntry extends EnvEntry {

	private VisibleType type;

	private VisibleType widestAssignment;

	private boolean isHidden;
	
	public VarEntry(VisibleType type, boolean isHidden, int lineOfDeclaration) {
		super(lineOfDeclaration);
		this.type = type;
		this.widestAssignment = null;
		this.isHidden = isHidden;
	}

	public VisibleType getType() {
		return type;
	}
	
	public boolean isHidden() {
		return isHidden;
	}
	
	public String toString() {
		return " variable";
	}

	public void setType(VisibleType type) {
		this.type = type;
	}

	public String getEntryKind() {
		return "variable";
	}

	public VisibleType getNarrowestType() {
		return widestAssignment;
	}

}
