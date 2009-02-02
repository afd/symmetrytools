package src.etch.error;


public class DuplicateInlineParametersError extends Error {

	private String inlineName;
	private String duplicateParameter;
	private int i;
	private int j;
	
	public DuplicateInlineParametersError(String inlineName, String duplicateParameter, int i, int j) {
		this.inlineName = inlineName;
		this.duplicateParameter = duplicateParameter;
		this.i = i;
		this.j = j;
	}

	@Override
	public String message() {
		return "Parameters " + i + " and " + j + " of inline macro \"" + inlineName + "\" have the same name, \"" + duplicateParameter + "\"";
	}

}
