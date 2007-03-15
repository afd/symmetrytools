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

public class EqMismatchError extends Error {

    public String leftType;
    public String rightType;
    public String operator;

    public EqMismatchError(String l, String r, String o) {
	leftType = l;
	rightType = r;
	operator = o;
    }

    public String message() {
	return "the operands of \"e1 " + operator + "e2\" should have the same type, but here \"e1\" has type \"" + leftType + "\" and \"e2\" has type \"" + rightType + "\"";
    } 

}
