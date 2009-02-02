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

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public class IfCondError extends Error {

    public Type type;

    public IfCondError(Type t) {
    	type = t;
    }

    @Override
    public String message() {
		return "the condition of \"(if->then:else)\" should have type \"bool\"" +
		    " but here it is \"" + Minimiser.minimise(type).name() + "\"";
    } 
    
    @Override
	public void applySubstitutions(Substituter substituter) {
		type = substituter.applySubstitutions(type);
    }
    

}
