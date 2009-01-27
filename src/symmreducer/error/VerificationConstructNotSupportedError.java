package src.symmreducer.error;

import src.etch.error.Error;
import src.promela.node.Token;

public class VerificationConstructNotSupportedError extends Error {

	private Token kindOfConstruct;
	
	public VerificationConstructNotSupportedError(Token kindOfConstruct) {
		this.kindOfConstruct = kindOfConstruct;
	}

	@Override
	public String message() {
		return "'" + kindOfConstruct.getText() + "' constructs are not yet supported by TopSPIN for symmetry reduction";
	}

}
