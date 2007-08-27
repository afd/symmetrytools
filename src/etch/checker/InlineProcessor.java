package src.etch.checker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import src.etch.env.InlineEntry;
import src.etch.error.NameAlreadyUsedError;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AInline;
import src.promela.node.AManyNameLst;
import src.promela.node.AOneNameLst;
import src.promela.node.PNameLst;
import src.promela.node.Token;

public abstract class InlineProcessor extends DepthFirstAdapter {

	protected Map<String,InlineEntry> inlines = new HashMap<String,InlineEntry>();

	protected abstract void addError(Token token, src.etch.error.Error error);
	
	public void caseAInline(AInline node) {
		InlineEntry existingInline = (InlineEntry) inlines.get(node.getName().getText());
		if(existingInline!=null) {
			addError(node.getName(),new NameAlreadyUsedError(node.getName().getText(),existingInline));
		} else {
			inlines.put(node.getName().getText(),new InlineEntry(toList(node.getNameLst()),node.getSequence(),node.getName().getLine()));		
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

	
}
