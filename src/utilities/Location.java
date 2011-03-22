package src.utilities;

public class Location {
	private String file;
	private int line;
	
	public Location(String file, int line)
	{
		this.file = file;
		this.line = line;
	}

	public String getFile() {
		return file;
	}

	public int getLine() {
		return line;
	}
	
}
