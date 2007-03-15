/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : SubtypingError.java                                      */
/* DESCRIPTION   : Error: a pair of types prove to have an inappropriate    */
/*                        subtyping relationship during unification         */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/****************************************************************************/

package src.etch.error;

public class SubtypingError extends Error {

    public String type1;
    public String type2;

    public SubtypingError(String t1, String t2) {
	type1 = t1;
	type2 = t2;
    }

    public String message() {
	return "type \"" + type1 + "\" occurs in a context where it is required to be a subtype of \"" + type2 + "\".";
	
    } 

}
