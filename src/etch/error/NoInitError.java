package src.etch.error;


public class NoInitError extends Error {

	public String message() {
		return "Symmetry detection only applicable for specifications which initiate processes using an 'init' process.";
	}

}
