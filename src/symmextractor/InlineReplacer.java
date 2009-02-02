package src.symmextractor;

import java.util.List;

import src.etch.checker.InlineProcessor;
import src.etch.env.InlineEntry;
import src.etch.error.Error;
import src.promela.node.AInlineSimpleStmnt;
import src.promela.node.Node;
import src.promela.node.TSeparator;
import src.promela.node.Token;

public class InlineReplacer extends InlineProcessor {

	private String inlinedProgram = "";

	public String getInlinedProgram() {
		return inlinedProgram;
	}

	public void defaultCase(Node node) {
		inlinedProgram = inlinedProgram + node;
	}

	public void caseTSeparator(TSeparator node) {
		inlinedProgram = inlinedProgram + node + "\n";
	}
	
	@Override
	public void caseAInlineSimpleStmnt(AInlineSimpleStmnt node) {
		InlineEntry inline = (InlineEntry) env.get(node.getName().getText());
		assert(null != inline);
		List<String> actualParametersAsStrings = toListOfStrings(node.getExprLst());
		assert(inline.getArity() == actualParametersAsStrings.size());
		inline.getSequenceWithSubstitutions(actualParametersAsStrings).apply(this);
	}
	
	protected void addError(Token token, Error error) {
	}
		
}
