/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : IncompatibleTypesError.java                              */
/* DESCRIPTION   : Error: types prove to be incompatible during unification */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 10th February 2005                                       */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 10th February 2005                                       */
/****************************************************************************/

package src.etch.error;

public class IncompatibleTypesError extends Error {

    public String type1;
    public String type2;

    public IncompatibleTypesError(String t1, String t2) {
	type1 = t1;
	type2 = t2;
    }

    public String message() {
	return "error during type unification: \"" + type1 + "\" is not compatible with type \"" + type2 + "\"";
	
    } 

}
