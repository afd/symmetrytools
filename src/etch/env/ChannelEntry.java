package src.etch.env;


public class ChannelEntry extends VarEntry {
	
	private int length;
	
	public ChannelEntry(VarEntry varEntry, int length) {
		super(varEntry.getType(),varEntry.isHidden());
		this.length = length;
	}
	
	public boolean equal(ChannelEntry other) {
		return getType().equal(other.getType()) && length == other.length;
	}
	
	public String toString() {
		return length + " of " + getType().name();
	}
	
	public int getLength() {
		return length;
	}
	
}
