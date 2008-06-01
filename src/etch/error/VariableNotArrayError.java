/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : VariableNotArrayError.java                               */
/* DESCRIPTION   : Error: non array variable used as array                  */
/*                                                                          */
/* AUTHOR        : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/*                                                                          */
/* LAST MODIFIED : S.J.Gay                                                  */
/* DATE          : 28th August 2003                                         */
/****************************************************************************/

package src.etch.error;

public class VariableNotArrayError extends Error {

	private String variableName;
    private String type;
    
    public VariableNotArrayError(String variableName, String type) {
    	this.variableName = variableName;
    	this.type = type;
    }

    public String message() {
	return "variable \"" + variableName + "\" is used as an array, but has type \"" + type + "\"";
    } 

}
