/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : MismatchedArgumentsError.java                            */
/* DESCRIPTION   : Error: channel arguments are found to have different     */
/*                        lengths during unification                        */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 10th February 2005                                       */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 10th February 2005                                       */
/****************************************************************************/

package src.etch.error;

public class MismatchedArgumentsError extends Error {
    
    private int length1;
    private int length2;

    public MismatchedArgumentsError(int length1, int length2) {
    	this.length1 = length1;
    	this.length2 = length2;
    }

    public String message() {
	return "arguments of lengths " + length1 + " and " + length2 + " have been used with the same channel.";
	
    } 

}
