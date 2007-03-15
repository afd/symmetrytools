package src.etch.error;

public class WrongNumArgsError extends Error {

	public String id;

	public Integer formalArity;

	public Integer actualArity;

	public WrongNumArgsError(String id, int formalArity, int actualArity) {
		this.id = id;
		this.formalArity = new Integer(formalArity);
		this.actualArity = new Integer(actualArity);
	}

	public String message() {
		return "\"" + id + "\" expects " + formalArity.toString()
				+ " arguments but " + actualArity.toString()
				+ " has been supplied.";
	}

}
