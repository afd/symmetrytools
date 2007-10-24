package src.etch.types;

public class TypeVariableFactory {

	private char letter;
	private int nextid;
	private boolean prettyPrint;
	
	public TypeVariableFactory(char letter, boolean prettyPrint) {
		this.letter = letter;
		this.prettyPrint = prettyPrint;
		nextid = 0;
	}

	public TypeVariableType freshTypeVariable() {
		return (new TypeVariableType(letter,nextid++, prettyPrint));
	}

}
