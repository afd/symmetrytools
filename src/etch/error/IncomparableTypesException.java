package src.etch.error;

import src.etch.types.ChanType;
import src.etch.types.Type;

@SuppressWarnings("serial")
public class IncomparableTypesException extends Exception {

	private Type left;

	private Type right;

	public IncomparableTypesException(Type left, Type right) {
		assert (! (left instanceof ChanType || right instanceof ChanType));
		this.left = left;
		this.right = right;
	}

	public Type getLeftType() {
		return left;
	}

	public Type getRightType() {
		return right;
	}

	@Override
	public String toString() {
		return "Error: attempted to compare types " + left.name() + " and " + right.name()
				+ ", which are not subtypes of one another.";
	}

	/* Note: there is no need to apply substitutions to the type fields of this error, 
	 * as they cannot be channels.  Similarly, the type expressions need not be minimized.
	 */

}
