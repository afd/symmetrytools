package src.etch.env;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

import src.etch.checker.NameSubstituter;
import src.promela.node.PSequence;

public class InlineEntry extends EnvEntry {

	private List<String> argNames;
	private PSequence sequence;
	
	public InlineEntry(List<String> argNames, PSequence sequence, int lineOfDeclaration) {
		super(lineOfDeclaration);
		this.argNames = argNames;
		this.sequence = sequence;
	}
	
	public PSequence getSequenceWithSubstitutions(List<String> actualArgNames) {
		Assert.assertEquals(argNames.size(),actualArgNames.size());
		Map<String,String> substitutions = new HashMap<String,String>();
		for(int i=0; i<argNames.size(); i++) {
			substitutions.put(argNames.get(i),actualArgNames.get(i));
		}
		PSequence result = (PSequence) sequence.clone();
		result.apply(new NameSubstituter(substitutions));
		return result;
	}

	public int getArity() {
		return argNames.size();
	}

	public String toString() {
		return "n inline macro";
	}

	public String getEntryKind() {
		return "inline macro";
	}
	
}
