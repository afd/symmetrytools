package src.etch.env;

public abstract class EnvEntry {

	private int lineOfDeclaration;

	public EnvEntry(int lineOfDeclaration) {
		this.lineOfDeclaration = lineOfDeclaration;
	}
	
	public abstract String getEntryKind();

	public int getLineOfDeclaration()
	{
		return lineOfDeclaration;
	}
}
