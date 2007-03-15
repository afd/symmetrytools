/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : VariableNotRecordError.java                              */
/* DESCRIPTION   : Error: non-record variable used as record                */
/*                                                                          */
/* AUTHOR        : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/*                                                                          */
/* LAST MODIFIED : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/****************************************************************************/

package src.etch.error;

public class VariableNotRecordError extends Error {

    public String typeName;

    public VariableNotRecordError(String t) {
	typeName = t;
    }

    public String message() {
	return "a variable is used as a record type, but it has type \"" + typeName + "\".";
    } 

}
