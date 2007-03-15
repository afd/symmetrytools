package src.etch.checker;

import src.etch.error.Error;

public class NoInitError extends Error {

	public String message() {
		return "Symmetry detection only applicable for specifications which initiate processes using an 'init' process.";
	}

}
