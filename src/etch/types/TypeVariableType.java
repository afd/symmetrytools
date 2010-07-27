package src.etch.types;



public class TypeVariableType extends SimpleType implements InternalType {

	private static char prettyVariables[] = { 'X', 'Y', 'Z', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z' };
	
	private char letter;
	private int guid;
	private Type lower;
	private Type upper;
	private boolean prettyPrint;
	
	protected TypeVariableType(char letter, int guid, boolean prettyPrint) {
		this.letter = letter;
		this.guid = guid;
		this.prettyPrint = prettyPrint;
		lower = BottomType.uniqueInstance;
		upper = TopType.uniqueInstance;
	}

	public String name() {
		
		if(lower.equal(upper))
		{
			return lower.name();
		}
		
		String result = (lower.equal(BottomType.uniqueInstance)) ? "" : lower.name() + " <: ";
		if(prettyPrint && guid < prettyVariables.length) {
			result += "" + prettyVariables[guid];
		} else {
			result += String.valueOf(letter) + guid;
		}
		
		return result + ((upper.equal(TopType.uniqueInstance)) ? "" : " <: " + upper.name());
	}

	public void setLower(Type lower) {
		this.lower = lower;
	}

	public void setUpper(Type upper) {
		this.upper = upper;
	}

	public Type getLower() {
		return lower;
	}

	public Type getUpper() {
		return upper;
	}

	public boolean isSubtype(Type t) {
		assert(false);
		return false;
	}

	@Override
	public String spinRepresentation() {
		assert(false);
		return null;
	}

}
