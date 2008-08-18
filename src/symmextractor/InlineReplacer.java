package src.symmextractor;

import java.util.ArrayList;
import java.util.List;


import src.etch.checker.InlineProcessor;
import src.etch.env.InlineEntry;
import src.etch.error.Error;
import src.promela.node.AInlineSimpleStmnt;
import src.promela.node.AManyExprLst;
import src.promela.node.AOneExprLst;
import src.promela.node.Node;
import src.promela.node.PExprLst;
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
	
	public void caseAInlineStmnt(AInlineSimpleStmnt node) {
		InlineEntry inline = (InlineEntry) inlines.get(node.getName().getText());
		assert(null != inline);
		List<String> actualParametersAsStrings = toList(node.getExprLst());
		assert(inline.getArity() == actualParametersAsStrings.size());
		inline.getSequenceWithSubstitutions(actualParametersAsStrings).apply(this);
	}
	
	private List<String> toList(PExprLst exprLst) {
		List<String> result = new ArrayList<String>();
		if(exprLst!=null) {
			PExprLst temp = exprLst;
			while(temp instanceof AManyExprLst) {
				result.add(((AManyExprLst)temp).getExpr().toString());
				temp = ((AManyExprLst)temp).getExprLst();
			}
			result.add(((AOneExprLst)temp).getExpr().toString());
		}
		return result;
	}

	protected void addError(Token token, Error error) {
	}
		
}
