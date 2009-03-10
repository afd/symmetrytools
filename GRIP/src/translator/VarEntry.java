package src.translator;

import java.util.HashSet;
import java.util.Set;

import src.exceptions.BadlyInitialisedVariableException;

public class VarEntry {

	private int lower;
	private int upper;
	private int init;
	
	public VarEntry(int lower, int upper, int init) throws BadlyInitialisedVariableException {
		this.lower = lower;
		this.upper = upper;
		this.init = init;
		
		if(init<lower || init>upper) {
			throw new BadlyInitialisedVariableException(lower,upper,init);
		}
	}

	public int getInit() {
		return init;
	}

	public int getLower() {
		return lower;
	}

	public int getUpper() {
		return upper;
	}
	
	public String toString() {
		return "[" + lower + ".." + upper + "] init " + init;
	}

	public Set<Integer> domain() {
		Set<Integer> result = new HashSet<Integer>();
		for(int i=lower; i<=upper; i++) {
			result.add(i);
		}
		return result;
	}
	
}
