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

import src.etch.typeinference.Substituter;
import src.etch.types.Type;

public class VariableNotRecordError extends Error {

    private Type type;
   
    private String reference;
    
    public VariableNotRecordError(String reference, Type type) {
    	this.reference = reference;
    	this.type = type;
    }

    public String message() {
    	return "variable \"" + reference + "\" is used as a record type, but it has type \"" + type.name() + "\"";
    } 

    @Override
	public void applySubstitutions(Substituter substituter) {
		type = substituter.applySubstitutions(type);
    }
    
}
