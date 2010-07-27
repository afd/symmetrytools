package src.group;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import src.promela.node.Node;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.StringHelper;

public class Permutation {

	private Map<Object,Object> theMap;
	
	/**
	 * Given a permutation in saucy form, this makes a Permutation object with
	 * reference to the specific channel diagram extractor passed in.
	 * 
	 * @param saucyPerm
	 *            The permutation in saucy form.
	 * @param extractor
	 *            The channel diagram extractor to which the permutation is going to be
	 *            applied.
	 */
	public Permutation(String perm, StaticChannelDiagramExtractor extractor, boolean isGapPerm) {
		if(isGapPerm) {
			constructPermutationFromGapString(perm,extractor);
		} else {
			constructPermutationFromSaucyString(perm, extractor);
		}
	}

	private void constructPermutationFromGapString(String perm, StaticChannelDiagramExtractor extractor) {
		
		theMap = new HashMap<Object,Object>();
		// The permutation is in d.c.f., so split it into disjoint cycles.
		StringTokenizer permSplitter = new StringTokenizer(perm, "()");
		while (permSplitter.hasMoreTokens()) {
			// Loop through each cycle.
			String cycle = StringHelper.removeWhitespace(permSplitter.nextToken());
			// Split each cycle into individual elements.
			StringTokenizer cycleSplitter = new StringTokenizer(cycle, ",");
			String first, previous, current = new String();
			first = cycleSplitter.nextToken();
			previous = first;
			while (cycleSplitter.hasMoreTokens()) {


				current = cycleSplitter.nextToken();

				// For each element of the cycle, add an entry to the map
				// indiciating
				// where the element is taken. Both the element and its
				// destination
				// are clarified in the context of the channel diagram.
				theMap.put(extractor.getScdNode(Integer.parseInt(previous)), extractor.getScdNode(Integer.parseInt(current)));
				previous = current;
			}
			// Add the last -> first to the map.
			theMap.put(extractor.getScdNode(Integer.parseInt(current)), extractor.getScdNode(Integer.parseInt(first)));
		}
	}

	private void constructPermutationFromSaucyString(String saucyPerm, StaticChannelDiagramExtractor extractor) {
		theMap = new HashMap<Object,Object>();
		// The permutation is in d.c.f., so split it into disjoint cycles.
		StringTokenizer permSplitter = new StringTokenizer(saucyPerm, "()");
		while (permSplitter.hasMoreTokens()) {
			// Loop through each cycle.
			String cycle = permSplitter.nextToken();
			// Split each cycle into individual elements.
			StringTokenizer cycleSplitter = new StringTokenizer(cycle, " ");
			String first, previous, current = new String();
			first = cycleSplitter.nextToken();
			previous = first;
			while (cycleSplitter.hasMoreTokens()) {
				current = cycleSplitter.nextToken();
				// For each element of the cycle, add an entry to the map
				// indiciating
				// where the element is taken. Both the element and its
				// destination
				// are clarified in the context of the channel diagram.
				theMap.put(extractor.getScdNodeForSaucyValue(Integer.parseInt(previous)), extractor.getScdNodeForSaucyValue(Integer.parseInt(current)));
				previous = current;
			}
			// Add the last -> first to the map.
			theMap.put(extractor.getScdNodeForSaucyValue(Integer.parseInt(current)), extractor.getScdNodeForSaucyValue(Integer.parseInt(first)));
		}
	}

	public String gapRepresentation(StaticChannelDiagramExtractor extractor) {
		String result = "";
		Set<Object> marked = new HashSet<Object>();
		for(Object o : theMap.keySet()) {
			assert(o instanceof String);
			if(!marked.contains(o)) {
				result += "(";
				boolean first = true;
				for(Object temp = o; !marked.contains(temp); temp = theMap.get(temp)) {
					assert(temp instanceof String);
					marked.add(temp);
					if(!first) {
						result += ",";
					} else {
						first = false;
					}
					result += extractor.getGapNumber((String)temp);
				}
				result += ")";
			}
		}
		return result;
	}

	/**
	 * Returns a string representation of the Permutation object for display and
	 * debugging purposes.
	 * 
	 * @return A string representation of the Permutation object.
	 */
	public String toString() {
		String result = "";
		Set<Object> toDealWith = new HashSet<Object>(theMap.keySet());

		while (!toDealWith.isEmpty()) {
			Iterator<Object> i = toDealWith.iterator();
			Object cycleStart = i.next();
			if (((String) cycleStart)
					.charAt(cycleStart.toString().length() - 1) == ' ')
				result = result
						+ "("
						+ cycleStart.toString().substring(0,
								cycleStart.toString().length() - 1);
			else
				result = result + "(" + cycleStart.toString();
			Object current = cycleStart;
			Object next = theMap.get(current);
			while (!next.equals(cycleStart)) {
				if (((String) next).charAt(next.toString().length() - 1) == ' ')
					result = result
							+ " "
							+ next.toString().substring(0,
									next.toString().length() - 1);
				else
					result = result + " " + next.toString();
				toDealWith.remove(current);
				current = next;
				next = theMap.get(current);
			}
			toDealWith.remove(current);
			result = result + ")";
		}

		return result;
	}

	/**
	 * Given an object, this returns the object which is obtained after applying
	 * the Permutation to the object.
	 * 
	 * @param o
	 *            The object which is to be permuted.
	 * @return The object which is obtained after the permutation has been
	 *         applied.
	 */
	public Object apply(Object o) {
		if (theMap.containsKey(o)) {
			return theMap.get(o);
		}
	    return o; // If the permutation does not act on o then return o
						// unchanged.
	}

	private Permutation()
	{
		theMap = new HashMap<Object,Object>(); 
	}

	public Permutation inverse() {
		Permutation result = new Permutation();
		Iterator<Object> i = this.theMap.keySet().iterator();
		while (i.hasNext()) {
			Object o1 = i.next();
			Object o2 = this.theMap.get(o1);
			result.theMap.put(o2, o1);
		}
		return result;
	}

	// Returns true if the permutation can be safely applied
	// to the abstract syntax tree.
	public boolean isSafeFor(Node theAST, StaticChannelDiagramExtractor typeInfo) {
		
		/* If you find yourself debugging this code, make sure you have executed
		 * apply_patch.pl, which fixes cloning in SableCC
		 */
		
		// Clone and normalise the original AST.
		Node normalizedAST = (Node) theAST.clone();
		normalizedAST.apply(new Normaliser(typeInfo.getNoProcesses()));

		// Apply the permutation to the original AST, and normalize the result
		theAST.apply(new Permuter(this, typeInfo));
		Node permutedAST = (Node) theAST.clone();
		permutedAST.apply(new Normaliser(typeInfo.getNoProcesses()));

		// Reverse the permutation to the original AST
		theAST.apply(new Permuter(this.inverse(), typeInfo));

		// Now check whether the normalized AST is the same as the permuted,
		// normalized AST.
		return new NodeComparator().compare(normalizedAST, permutedAST) == 0;
	}


}
