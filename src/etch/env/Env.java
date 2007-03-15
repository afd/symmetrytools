package src.etch.env;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import junit.framework.Assert;
import src.etch.types.TypeSubstituter;


/* An environment is a vector of hash tables, used as a stack.
 The 'put' method adds an entry to the hash table at the top of the stack
 (first element of the vector). The 'get' method searches down the stack.
 The 'openScope' method creates a new hash table on the top of the stack.
 The 'closeScope' method removes the top-most hash table. */

public class Env {

	private Vector<Map<String,EnvEntry>> stack;

	public Env() {
		stack = new Vector<Map<String,EnvEntry>>(1, 1);
		stack.addElement(new HashMap<String,EnvEntry>());
	}

	public void openScope() {
		stack.addElement(new HashMap<String,EnvEntry>());
	}

	public void closeScope() {
		stack.removeElementAt(stack.size() - 1);
	}

	public EnvEntry putGlobal(String n, EnvEntry e) {
		// This is necessary when adding proctypes.  It is a bit clumsy, and a better
		// solution could possibly be found.
		EnvEntry result = get(n);
		stack.elementAt(0).put(n, e);
		return result;
	}

	public EnvEntry put(String n, EnvEntry e) {
		return stack.elementAt(stack.size() - 1).put(n, e);
	}

	public EnvEntry get(String n) {
		for (int i = stack.size() - 1; i >= 0; i--) {
			EnvEntry e = (EnvEntry) stack.elementAt(i).get(n);
			if (e != null)
				return e;
		}
		return null;
	}

	public EnvEntry getLocal(String n) {
		// Only searches the current scope
		return stack.elementAt(stack.size() - 1).get(n);

	}

	public Map<String,EnvEntry> getTopEntries() {
		return stack.elementAt(stack.size() - 1);
	}
	
	public Map<String,ProctypeEntry> getProctypeEntries() {
		Map<String,ProctypeEntry> result = new HashMap<String,ProctypeEntry>();

		for(Iterator<String> i = stack.elementAt(0).keySet().iterator(); i.hasNext(); ) {
			String s = i.next();
			EnvEntry e = stack.elementAt(0).get(s);
			if (e instanceof ProctypeEntry)
				result.put(s, (ProctypeEntry)e);
		}
		return result;
	}

	public Map getChannelEntries() {
		Map<String,ChannelEntry> result = new HashMap<String,ChannelEntry>();

		for(Iterator<String> i = stack.elementAt(0).keySet().iterator(); i.hasNext(); ) {
			String s = i.next();
			EnvEntry e = stack.elementAt(0).get(s);
			if (e instanceof ChannelEntry)
				result.put(s, (ChannelEntry)e);
		}
		return result;
	}

	public void applySubsitutions(TypeSubstituter substituter) {

		Assert.assertTrue(stack.size()==1);

		for(Iterator<EnvEntry> i = stack.elementAt(0).values().iterator(); i.hasNext();) {
			EnvEntry e = i.next();
			if(e instanceof VarEntry) {
				((VarEntry)e).setType(substituter.applySubstitutions(((VarEntry)e).getType()));
			}
			
			if(e instanceof ProctypeEntry) {
				Map<String,EnvEntry> localScope = ((ProctypeEntry)e).getLocalScope();

				for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
					String name = iter.next();
					if(localScope.get(name) instanceof VarEntry) {
						((VarEntry)localScope.get(name)).setType(substituter.applySubstitutions(
								((VarEntry)localScope.get(name)).getType()));
					}
				}
			}			
		}
	}

	public void restoreScope(Map<String, EnvEntry> localScope) {
		stack.addElement(localScope);
	}

}
