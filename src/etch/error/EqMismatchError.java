/****************************************************************************/
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : EqMismatchError.java                                     */
/* DESCRIPTION   : Error: operands to (in)equality test have incomparable   */
/*                                                                          */
/* AUTHOR        : A.F. Donaldson                                           */
/* DATE          : 9th November 2004                                        */
/*                                                                          */
/* LAST MODIFIED : A.F. Donaldson                                           */
/* DATE          : 9th November 2004                                        */
/****************************************************************************/

package src.etch.error;

import src.etch.typeinference.Substituter;
import src.etch.types.Minimiser;
import src.etch.types.Type;
import src.promela.node.ACompoundEqExpr;
import src.utilities.StringHelper;

public class EqMismatchError extends Error {

    public Type leftType;
    public Type rightType;
    public ACompoundEqExpr node;

    public EqMismatchError(Type leftType, Type rightType, ACompoundEqExpr node) {
	this.leftType = leftType;
	this.rightType = rightType;
	this.node = node;
    }

    public String message() {
	return "the operands of \"e1" + node.getEqop().getText() + "e2\" should have the same type, but here \"" +
	StringHelper.removeWhitespace(node.getRelExpr().toString())
	   + "\" has type \"" + Minimiser.minimise(leftType).name() + "\" and \"" + StringHelper.removeWhitespace(node.getEqExpr().toString()) + "\" has type \"" + Minimiser.minimise(rightType).name() + "\"";
    } 
    
    @Override
	public void applySubstitutions(Substituter substituter) {
		leftType = substituter.applySubstitutions(leftType);
		rightType = substituter.applySubstitutions(rightType);
    }


}
