package src.etch.error;

public class ElementDoesNotExistError extends Error {

	private String name;
	private String kindOfElement;
	private String recordTypeName;
	
	public ElementDoesNotExistError(String name, String kindOfElement) {
		this.name = name;
		this.kindOfElement = kindOfElement;
		recordTypeName = null;
	}

	public ElementDoesNotExistError(String name, String kindOfElement, String recordTypeName) {
		this(name,kindOfElement);
		this.recordTypeName = recordTypeName;
	}

	public String message() {
		String result = "No " + kindOfElement + " named \"" + name + "\" exits";
		if(recordTypeName!=null) {
			result = result + " in user defined type \"" + recordTypeName + "\"";
		}
		return result + ".";
	}

}
