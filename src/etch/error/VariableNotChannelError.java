/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : VariableNotChannelError.java                             */
/* DESCRIPTION   : Error: non array variable used as array                  */
/*                                                                          */
/* AUTHOR        : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/*                                                                          */
/* LAST MODIFIED : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/****************************************************************************/

package src.etch.error;

public class VariableNotChannelError extends Error {

    public String type;

    public VariableNotChannelError(String t) {
	type = t;
    }

    public String message() {
	return "a channel operation can only be applied to a channel variable, but here one has been applied to a variable of type \"" + type + "\".";
    } 

}
