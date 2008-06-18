package src.symmextractor.error;

import src.etch.error.Error;
import src.etch.types.PidType;
import src.promela.node.Token;

public class UnaryArithmeticOnPidError extends Error {

	private String lValue;
	private Token operator;
	
	public UnaryArithmeticOnPidError(String lValue, Token operator) {
		this.lValue = lValue;
		this.operator = operator;
	}

	@Override
	public String message() {
		return "Cannot apply unary operator \"" + operator.getText() + "\" to \"" + lValue + "\" which has type " + (new PidType()).name();
	}

}
