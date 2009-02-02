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

import src.etch.types.ChanType;
import src.etch.types.Type;
import src.promela.node.Token;

public class VariableNotChannelError extends Error {

    private Type type;
    private Token chanop;
    
    public VariableNotChannelError(Type type, Token chanop) {
    	assert(!(type instanceof ChanType));
    	this.type = type;
    	this.chanop = chanop;
    }

    public String message() {
    	return "The \"" + chanop.getText() + "\" operator can only be applied a channel variable; here it has been applied to a variable of type \"" + type.name() + "\"";
    }
    
    /* There is no need to override the applySubstitutions, since "type" cannot be a channel */

}
