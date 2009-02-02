/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : IfMismatchError.java                                     */
/* DESCRIPTION   : Error: conditional branches have incompatible types      */
/*                                                                          */
/* AUTHOR        : A.F.Donaldson                                            */
/* DATE          : 9th June 2005                                            */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th June 2005                                            */
/****************************************************************************/

package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;

public class IfMismatchError extends Error {

    public Type thenType;
    public Type elseType;

    public IfMismatchError(Type t, Type u) {
	thenType = t;
	elseType = u;
    }

    public String message() {
	return "the branches of \"(if->then:else)\" should have compatible types " +
	    "but here the \"then\" branch has type \"" + Minimiser.minimise(thenType).name() + "\" " +
	    "and the \"else\" branch has type \"" + Minimiser.minimise(elseType).name() + "\""; 
    } 

    @Override
	public void applySubstitutions(Substituter substituter) {
		thenType = substituter.applySubstitutions(thenType);
		elseType = substituter.applySubstitutions(elseType);
    }

}
