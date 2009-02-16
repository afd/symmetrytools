package src.symmreducer.error;

import src.etch.error.Error;
import src.promela.node.TName;
import src.promela.node.Token;
import src.utilities.StringHelper;

public class VerificationConstructNotSupportedError extends Error {

	private Token kindOfConstruct;
	
	public VerificationConstructNotSupportedError(Token kindOfConstruct) {
		this.kindOfConstruct = kindOfConstruct;
	}

	@Override
	public String message() {
		return "'" + textForConstruct() + "' constructs are not yet supported by TopSPIN for symmetry reduction";
	}

	private String textForConstruct() {
		if(kindOfConstruct instanceof TName) {
			if(StringHelper.isAcceptLabelName(kindOfConstruct.getText())) {
				return "accept";
			}

			assert (StringHelper.isProgressLabelName(kindOfConstruct.getText()));
			return "progress";
		}
		
		return kindOfConstruct.getText();
	}

}
