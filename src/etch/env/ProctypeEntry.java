package src.etch.env;

import java.util.*;

import src.etch.types.Type;
import src.utilities.StringHelper;

public class ProctypeEntry extends EnvEntry {

	private List<Type> argTypes;
	private List<String> argNames;
	private Set<String> outChannels;
	private Set<String> inChannels;	

	private Map<String,EnvEntry> localScope;

	public static final ProctypeEntry initProctypeEntry = new ProctypeEntry(new ArrayList<Type>(),new ArrayList<String>());
	public static final String initProctypeName = "init_proctype";

	public ProctypeEntry(List<Type> argTypes, List<String> argNames) {
		this.argTypes = argTypes;
		this.argNames = argNames;
		outChannels = new HashSet<String>();
		inChannels = new HashSet<String>();
	}
	
	public List<Type> getArgTypes() {
		return Collections.unmodifiableList(argTypes);
	}

	public List<String> getArgNames() {
		return Collections.unmodifiableList(argNames);
	}
	
	public void addOutChannelName(String name) {
		outChannels.add(StringHelper.removeWhitespace(name));
	}

	public void addInChannelName(String name) {
		inChannels.add(StringHelper.removeWhitespace(name));
	}
	
	public Set<String> getOutChannels() {
		return Collections.unmodifiableSet(outChannels);
	}

	public Set<String> getInChannels() {
		return Collections.unmodifiableSet(inChannels);
	}
	
	public String toString() {
		return "proctype, in: " + inChannels + " out: " + outChannels;
	}

	public void setLocalVariableTypeInfo(Map<String,EnvEntry> localScope) {
		this.localScope = localScope;
	}
	
	public Map<String,EnvEntry> getLocalScope() {
		return localScope;
	}
	
}
