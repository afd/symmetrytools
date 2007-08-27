package src.etch.env;


public class ChannelEntry extends VarEntry {
	
	private int length;
	
	public ChannelEntry(VarEntry varEntry, int length, int lineOfDeclaration) {
		super(varEntry.getType(),varEntry.isHidden(),lineOfDeclaration);

		/* Actually, in Promela it is illegal to declare hidden channels.  Etch
		 * allows this, but could be changed so that an errir is thrown if
		 * varEntry.isHidden() returns true.
		 */
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

	public String getEntryKind()
	{
		return "channel";
	}
	
}
