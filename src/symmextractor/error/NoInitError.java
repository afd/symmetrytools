package src.symmextractor.error;

import src.etch.error.Error;


public class NoInitError extends Error {

	public String message() {
		return "No 'init' process was found.  Symmetry detection only applicable for specifications which initiate running processes via an 'init' process";
	}

}
