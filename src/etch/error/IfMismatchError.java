/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : IfMismatchError.java                                     */
/* DESCRIPTION   : Error: conditional branches have incompatible types      */
/*                                                                          */
/* AUTHOR        : A.F.Donaldson                                            */
/* DATE          : 9th June 2005                                            */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/****************************************************************************/

package src.etch.error;

public class IfMismatchError extends Error {

    public String thenType;
    public String elseType;

    public IfMismatchError(String t, String u) {
	thenType = t;
	elseType = u;
    }

    public String message() {
	return "the branches of \"(if->then:else)\" should have compatible types " +
	    "but here the \"then\" branch has type \"" + thenType + "\" " +
	    "and the \"else\" branch has type \"" + elseType + "\""; 
    } 

}
