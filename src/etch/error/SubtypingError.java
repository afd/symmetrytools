/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : SubtypingError.java                                      */
/* DESCRIPTION   : Error: a pair of types prove to have an inappropriate    */
/*                        subtyping relationship during unification         */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/****************************************************************************/

package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public class SubtypingError extends Error {

    public Type type1;
    public Type type2;

    public SubtypingError(Type type1, Type type2) {
		this.type1 = type1;
		this.type2 = type2;
    }

    public String message() {
    	return "Type \"" + Minimiser.minimise(type1).name() + "\" occurs in a context where it is required to be a subtype of \"" + Minimiser.minimise(type2).name() + "\"";
    }
    
    @Override
	public void applySubstitutions(Substituter substituter) {
		type1 = substituter.applySubstitutions(type1);
		type2 = substituter.applySubstitutions(type2);
    }

}
