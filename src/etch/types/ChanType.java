package src.etch.types;

import java.util.List;

public class ChanType extends Type {

	private Type messageType;

	public ChanType(Type messageType) {
		this.messageType = messageType;
	}

	public ChanType(List<Type> messageFieldTypes) {
		this.messageType = new ProductType(messageFieldTypes);
	}
	
	public Type getMessageType() {
		return messageType;
	}
	
	public boolean isSubtype(Type t) {
		return t.equal(this);
	}
	
	protected void setMessageType(Type t) {
		messageType = t;
	}
	
}
