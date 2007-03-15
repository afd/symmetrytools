package src.etch.env;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


public class ProcessEntry extends EnvEntry {

	public static final ProcessEntry initProcess = new ProcessEntry(ProctypeEntry.initProctypeName,new ArrayList<String>());
	private String proctypeName;
	private List<String> parameterNames;
	
	public ProcessEntry(String proctypeName, List<String> parameterNames) {
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

}
