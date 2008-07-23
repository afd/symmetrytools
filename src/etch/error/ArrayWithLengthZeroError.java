package src.etch.error;


public class ArrayWithLengthZeroError extends Error {

	private String name;
	
	public ArrayWithLengthZeroError(String name) {
		this.name = name;
	}

	public String message() {
		return "Array \"" + name + "\" has size 0 -- array sizes must be positive";
	}

}
