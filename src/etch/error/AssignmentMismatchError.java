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

import src.etch.types.Type;

public class AssignmentMismatchError extends SubtypingError {

    public AssignmentMismatchError(Type v, Type e) {
    	super(e,v);
    }

    public String message() {
    	return "invalid assignment -- " + super.message();
    } 

}
