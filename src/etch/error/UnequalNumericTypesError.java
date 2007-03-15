/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : UnequalNumericTypesError.java                            */
/* DESCRIPTION   : Error: numeric types prove to be unequal during          */
/*                        unification of channel fields                     */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/****************************************************************************/

package src.etch.error;

public class UnequalNumericTypesError extends Error {

    public String type1;
    public String type2;

    public UnequalNumericTypesError(String t1, String t2) {
	type1 = t1;
	type2 = t2;
    }

    public String message() {
	return "error during type unification: numeric types \"" + type1 + "\" and \"" + type2 + "\" occur in a context where they should be equal.";
	
    } 

}
