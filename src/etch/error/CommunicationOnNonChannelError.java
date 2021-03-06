package src.etch.error;


import src.etch.types.ChanType;
import src.etch.types.Type;
import src.promela.node.Token;

public class CommunicationOnNonChannelError extends Error {

	private Token operator;
	private Type type;
	
	public CommunicationOnNonChannelError(Token operator, Type type) {
		assert(!(type instanceof ChanType));
		this.operator = operator;
		this.type = type;
	}

	@Override
	public String message() {
		return "Operator " + operator.getText() + " cannot be applied to an expression with type " + type.name();
	}
	
	/* Note: there is no need to apply substitutions to the type field of this error, as it cannot
	 * be a channel.  Similarly, the type expression need not be minimized.
	 */

}
