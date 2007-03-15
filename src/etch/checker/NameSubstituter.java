package src.etch.checker;

import java.util.Map;

import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.TName;

public class NameSubstituter extends DepthFirstAdapter {

	private Map nameSubstitutions;
	
	public NameSubstituter(Map nameSubstitutions) {
		this.nameSubstitutions = nameSubstitutions;
	}
	
	public void caseTName(TName node) {
		if(nameSubstitutions.get(node.getText())!=null) {
			node.setText((String)nameSubstitutions.get(node.getText()));
		}
	}

}
