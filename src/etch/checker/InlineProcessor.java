package src.etch.checker;

import java.util.ArrayList;
import java.util.List;

import src.etch.env.Environment;
import src.etch.env.InlineEntry;
import src.etch.error.DuplicateInlineParametersError;
import src.etch.error.NameAlreadyUsedError;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AInline;
import src.promela.node.AManyExprLst;
import src.promela.node.AManyNameLst;
import src.promela.node.AOneExprLst;
import src.promela.node.AOneNameLst;
import src.promela.node.PExprLst;
import src.promela.node.PNameLst;
import src.promela.node.POrExpr;
import src.promela.node.Token;

public abstract class InlineProcessor extends DepthFirstAdapter {

	protected Environment env = new Environment();

	protected abstract void addError(Token token, src.etch.error.Error error);

	protected boolean nameExists(String name) {
		return env.get(name) != null;
	}
	
	public void caseAInline(AInline node) {
		if(nameExists(node.getName().getText())) {
			addError(node.getName(), new NameAlreadyUsedError(node.getName().getText(), env.get(node.getName().getText())));
		} else {
			List<String> parameterNames = toList(node.getNameLst());
			for(int i=1; i<parameterNames.size(); i++) {
				for(int j=0; j<i; j++) {
					if(parameterNames.get(i).equals(parameterNames.get(j))) {
						addError(node.getName(), new DuplicateInlineParametersError(node.getName().getText(), parameterNames.get(i), j+1, i+1));
					}
				}
			}
			
			env.put(node.getName().getText(),new InlineEntry(parameterNames,node.getSequence(),node.getName().getLine()));
		}
	}

	private List<String> toList(PNameLst nameLst) {
		List<String> result = new ArrayList<String>();
		
		if(nameLst==null) {
			return result;
		}
		
		PNameLst temp = nameLst;
		
		while(temp instanceof AManyNameLst) {
			result.add(((AManyNameLst)temp).getName().getText());
			temp = ((AManyNameLst)temp).getNameLst();
		}
		
		result.add(((AOneNameLst)temp).getName().getText());
		return result;
	}

	protected List<String> toListOfStrings(PExprLst exprLst) {
		List<String> result = new ArrayList<String>();

		if(null == exprLst) {
			return result;
		}

		PExprLst temp = exprLst;
		
		while(temp instanceof AManyExprLst) {
			result.add(((AManyExprLst)temp).getOrExpr().toString());
			temp = ((AManyExprLst)temp).getExprLst();
		}
		result.add(((AOneExprLst)temp).getOrExpr().toString());
		return result;
	}

	protected List<POrExpr> toListOfExpressions(PExprLst exprLst) {
		List<POrExpr> result = new ArrayList<POrExpr>();

		if(null == exprLst) {
			return result;
		}

		PExprLst temp = exprLst;
		
		while(temp instanceof AManyExprLst) {
			result.add(((AManyExprLst)temp).getOrExpr());
			temp = ((AManyExprLst)temp).getExprLst();
		}
		result.add(((AOneExprLst)temp).getOrExpr());
		return result;
	}
	
	
}
