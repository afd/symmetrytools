/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : AssignmentMismatchError.java                             */
/* DESCRIPTION   : Error: assignment operands have unsuitable types         */
/*                                                                          */
/* AUTHOR        : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/*                                                                          */
/* LAST MODIFIED : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/****************************************************************************/

package src.etch.error;

public class AssignmentMismatchError extends SubtypingError {

    public AssignmentMismatchError(String v, String e) {
    	super(e,v);
    }

    public String message() {
    	return "error in assignment -- " + super.message();
    } 

}
