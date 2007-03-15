package src.group;

import java.util.*;
import src.promela.node.Node;

/**
 * This implementation of the Comparator interface allows two nodes of an
 * abstract syntax tree to be compared.  This is useful for a) checking
 * textual equality of abstract syntax trees (to determine whether or not
 * a permutation is consistent), and b) to normalise abstract syntax trees
 * (e.g. for sorting options of if and do statements into lexicographic order.
 * 
 * @author      Alastair Donaldson
 * @version     1.0 (15/09/04)
 * @since       1.0 (15/09/04)
 */
public class NodeComparator implements Comparator<Node> {
 
    /**
     * Given two Node objects, returns 0 if they are equal, a positive
     * value if a is greater than b, and a negative value otherwise
     *
     * @param  a  The first object to be compared.
     * @param  b  The second object to be compared.
     * @return    0 if a equals b, > 0 if a is greater than b, < 0 otherwise
     */      
    public int compare(Node a, Node b) {
    	return a.toString().compareTo(b.toString());
    }
    
}
