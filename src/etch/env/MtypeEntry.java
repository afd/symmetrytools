package src.etch.env;

public class MtypeEntry extends EnvEntry {

	public MtypeEntry(int lineOfDeclaration)
	{
		super(lineOfDeclaration);
	}
	
	public String toString() {
		return " message type";
	}

	public String getEntryKind() {
		return "message type (mtype)";
	}
	
}
