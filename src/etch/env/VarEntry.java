package src.etch.env;

import src.etch.types.Type;

public class VarEntry extends EnvEntry {

	private Type type;
	private boolean isHidden;
	
	public VarEntry(Type type, boolean isHidden) {
		this.type = type;
		this.isHidden = isHidden;
	}

	public Type getType() {
		return type;
	}
	
	public boolean isHidden() {
		return isHidden;
	}
	
	public String toString() {
		return " variable";
	}

	public void setType(Type type) {
		this.type = type;
	}
}
