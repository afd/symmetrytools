package src.etch.checker;

import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.Node;
import src.promela.node.Token;

public class LineCounter extends DepthFirstAdapter {

	private int maxLine;
	
	public LineCounter() {
		maxLine = 0;
	}

    public void defaultCase(Node node)
    {
    	if(node instanceof Token) {
    		if(((Token)node).getLine() > maxLine) {
    			maxLine = ((Token)node).getLine();
    		}
    	}
    }
    
    public int numberOfLines() {
    	return maxLine;
    }
	
}
