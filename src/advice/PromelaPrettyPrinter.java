package src.advice;

import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AAtomicCompoundStmnt;
import src.promela.node.ABracesCompoundStmnt;
import src.promela.node.ADeclarationStep;
import src.promela.node.ADoSimpleStmnt;
import src.promela.node.ADstepCompoundStmnt;
import src.promela.node.AIfSimpleStmnt;
import src.promela.node.AInit;
import src.promela.node.AMtypeModule;
import src.promela.node.ANormalOptions;
import src.promela.node.AProctype;
import src.promela.node.AStatementStep;
import src.promela.node.Node;

public class PromelaPrettyPrinter extends DepthFirstAdapter {
	
	private static final int INDENT_LEVEL = 3;
	
	private String stringRepresentation; 
	private int indentation;
	
	public PromelaPrettyPrinter() {
		stringRepresentation = "";
		indentation = 0;
	}
	
	private void increaseIndentation() {
		indentation += INDENT_LEVEL;
	}

	private void decreaseIndentation() {
		indentation -= INDENT_LEVEL;
	}
	
    public void defaultCase(Node node)
    {
    	stringRepresentation += node.toString();
    }
    
    public void inAProctype(AProctype node) {
    	stringRepresentation += "\n";
    	increaseIndentation();
    }
    
    public void outAProctype(AProctype node) {
    	stringRepresentation += "\n";
    	decreaseIndentation();
    }
    
    public void inAStatementStep(AStatementStep node) {
    	stringRepresentation += "\n"; indent();
    }

    public void inADeclarationStep(ADeclarationStep node) {
    	stringRepresentation += "\n"; indent();
    }
    
    public void caseADoSimpleStmnt(ADoSimpleStmnt node) {
    	stringRepresentation += "\n"; indent();
    	stringRepresentation += "do";
    	node.getOptions().apply(this);
    	stringRepresentation += "\n"; indent();
    	stringRepresentation += "od";    	
    }

    public void caseAIfSimpleStmnt(AIfSimpleStmnt node) {
    	stringRepresentation += "\n"; indent();
    	stringRepresentation += "if";
    	node.getOptions().apply(this);
    	stringRepresentation += "\n"; indent();
    	stringRepresentation += "fi";    	
    }
    
    public void caseANormalOptions(ANormalOptions node) {
    	stringRepresentation += "\n"; indent();
    	stringRepresentation += "::";
    	increaseIndentation();
    	node.getSequence().apply(this);
    	decreaseIndentation();
    	if(null != node.getOptions()) {
    		node.getOptions().apply(this);
    	}
    }
    
    public void inAMtypeModule(AMtypeModule node) {
    	stringRepresentation += "\n";
    }

	private void indent() {
		for(int i = 0; i < indentation; i++) {
			stringRepresentation += " ";
		}
	}

	public String getString() {
		return stringRepresentation;
	}

	public void caseAAtomicCompoundStmnt(AAtomicCompoundStmnt node) {
		stringRepresentation += "\n";
		indent();
		stringRepresentation += "atomic {";
		increaseIndentation();
		node.getSequence().apply(this);
		handleClosingBrace();
	}

	public void caseADstepCompoundStmnt(ADstepCompoundStmnt node) {
		stringRepresentation += "\n";
		indent();
		stringRepresentation += "d_step {";
		increaseIndentation();
		node.getSequence().apply(this);
		handleClosingBrace();
	}
	
	public void caseABracesCompoundStmnt(ABracesCompoundStmnt node) {
		stringRepresentation += "\n";
		indent();
		stringRepresentation += "{";
		increaseIndentation();
		node.getSequence().apply(this);
		handleClosingBrace();
	}

	private void handleClosingBrace() {
		decreaseIndentation();
		stringRepresentation += "\n";
		indent();
		stringRepresentation += "}";
		
	}
	
	public void caseAInit(AInit node) {
		stringRepresentation += "\ninit {";
		increaseIndentation();
		node.getSequence().apply(this);
		decreaseIndentation();
		stringRepresentation += "\n}\n";
	}

}
