package src.etch.env;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;




public class ProcessEntry extends EnvEntry {

	public static final ProcessEntry initProcess = new ProcessEntry(ProctypeEntry.initProctypeName,new ArrayList<String>());
	private String proctypeName;
	private List<String> parameterNames;
	
	public ProcessEntry(String proctypeName, List<String> parameterNames) {
		super(-1);
		this.proctypeName = proctypeName;
		this.parameterNames = parameterNames;
	}
	
	public String getProctypeName() {
		return proctypeName;
	}
	
	public List<String> getParameterNames() {
		return Collections.unmodifiableList(parameterNames);
	}
	
	public String toString() {
		return proctypeName + "(" + parameterNames + ")";
	}

	public String getEntryKind() {
		assert(false);
		/* This method should not be called on a process entry,
		 * as it is only called when a user has declared duplicate-named
		 * entries, and the user doesn't declare named process entries
		 * (unlike named proctypes, which the user does indeed declare)
		 */
		return null;
	}

	public int getLineOfDeclaration() {
		assert(false);
		return super.getLineOfDeclaration();
	}
}
