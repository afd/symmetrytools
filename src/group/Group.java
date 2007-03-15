package src.group;

import java.util.*;

import src.symmextractor.StaticChannelDiagramExtractor;

/**
 * Group is a concrete class used to represent groups of Permutation objects. A
 * group is represented by a set of generators.
 * 
 * The class has default access so that it is only visible within the group
 * package.
 * 
 * @author Alastair Donaldson
 * @version 1.1 (11/10/04) -- added add method and empty constructor
 * @since 1.0 (15/09/04)
 */
public class Group {
	private Set<Permutation> generators;
	
	public Group(String saucyGens, StaticChannelDiagramExtractor extractor) {
		generators = new HashSet<Permutation>();
		for(StringTokenizer strtok = new StringTokenizer(saucyGens,"\n"); strtok.hasMoreTokens();) {
			generators.add(new Permutation(strtok.nextToken(),extractor,false));
		}
	}

	public Group(Set<Permutation> generators) {
		this.generators = generators;
	}
	
	public Iterator<Permutation> iterator() {
		return generators.iterator();
	}

	public String toString() {
		if (isTrivialGroup()) {
			return "{id}";
		}
		String result = "<";
		Iterator i = generators.iterator();
		while (i.hasNext()) {
			result = result + i.next().toString();
			if (i.hasNext()) {
				result = result + ",";
			}
		}
		return result + ">";
	}

	public String gapGenerators(StaticChannelDiagramExtractor extractor) {
		if(isTrivialGroup()) {
			return "Group(());";
		}
		
		String result = "Group(";
		
		for(Iterator<Permutation> iter = generators.iterator(); iter.hasNext();) {
			result += iter.next().gapRepresentation(extractor);
			if(iter.hasNext()) {
				result += ",";
			}
		}
		
		return result + ");";
	}
	
	private boolean isTrivialGroup() {
		return generators.isEmpty();
	}

	public int noGenerators() {
		return generators.size();
	}
}
