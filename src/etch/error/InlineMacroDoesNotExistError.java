package src.etch.error;

public class InlineMacroDoesNotExistError extends Error {

	private String name;
	
	public InlineMacroDoesNotExistError(String name) {
		this.name = name;
	}

	@Override
	public String message() {
		return "no inline macro named \"" + name + "\" has been defined";
	}

}
