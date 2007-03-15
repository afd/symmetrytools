/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : IfCondError.java                                         */
/* DESCRIPTION   : Error: non-boolean condition in conditional              */
/*                                                                          */
/* AUTHOR        : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/*                                                                          */
/* LAST MODIFIED : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/****************************************************************************/

package src.etch.error;

public class IfCondError extends Error {

    public String type;

    public IfCondError(String t) {
	type = t;
    }

    public String message() {
	return "the condition of \"(if->then:else)\" should have type \"bool\"" +
	    " but here it is \"" + type + "\"";
    } 

}
