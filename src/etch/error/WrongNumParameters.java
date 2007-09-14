package src.etch.error;

public class WrongNumParameters extends Error {

	public String id;

	public Integer formalArity;

	public Integer actualArity;

	public WrongNumParameters(String id, int formalArity, int actualArity) {
		this.id = id;
		this.formalArity = new Integer(formalArity);
		this.actualArity = new Integer(actualArity);
	}

	public String message() {
		String result = "\"" + id + "\" expects " + formalArity
				+ " parameter";
		if(formalArity!=1) {
			result += "s";
		}
		result += ", but " + actualArity + " ";
		if(actualArity==1) {
			result += "has";
		} else {
			result += "have";
		}
		result += " been supplied";
		return result;
	}

}
