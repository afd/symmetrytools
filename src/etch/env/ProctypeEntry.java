package src.etch.env;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import junit.framework.Assert;
import src.etch.types.VisibleType;
import src.utilities.StringHelper;

public class ProctypeEntry extends EnvEntry {

	private List<VisibleType> argTypes;
	private List<String> argNames;
	private Set<String> outChannels;
	private Set<String> inChannels;	

	private Map<String,EnvEntry> localScope;

	public static final ProctypeEntry initProctypeEntry = new ProctypeEntry(new ArrayList<VisibleType>(),new ArrayList<String>(),-1);
	public static final String initProctypeName = "init";

	public ProctypeEntry(List<VisibleType> argTypes, List<String> argNames, int lineOfDeclaration) {
		super(lineOfDeclaration);
		this.argTypes = argTypes;
		this.argNames = argNames;
		outChannels = new HashSet<String>();
		inChannels = new HashSet<String>();
	}
	
	public List<VisibleType> getArgTypes() {
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

	public String getEntryKind() {
		return "proctype";
	}

	public int getLineOfDeclaration()
	{
		if(this.equals(initProctypeEntry) && super.getLineOfDeclaration()==-1)
		{
			Assert.assertTrue(false);
		}
		return super.getLineOfDeclaration();
	}
}
