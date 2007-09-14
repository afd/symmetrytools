package src.etch.error;


public class BadlyFormedInitError extends Error {

	public String message() {
		return "The 'init' process must have the form 'init { atomic { <run statements>; <other statements>? }; <more statements>? } }";
	}

}
