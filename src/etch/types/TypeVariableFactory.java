package src.etch.types;

public class TypeVariableFactory {

	private char letter;
	private int nextid;

	public TypeVariableFactory(char letter) {
		this.letter = letter;
		nextid = 0;
	}

	public TypeVariableType freshTypeVariable() {
		return (new TypeVariableType(letter,nextid++));
	}

}
