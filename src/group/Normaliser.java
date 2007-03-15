package src.group;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import junit.framework.Assert;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AAtomicStmnt;
import src.promela.node.ACompoundAndExpr;
import src.promela.node.ACompoundOrExpr;
import src.promela.node.AInit;
import src.promela.node.AManySequence;
import src.promela.node.ANormalOptions;
import src.promela.node.ANullSequence;
import src.promela.node.AOneSequence;
import src.promela.node.ASimpleAndExpr;
import src.promela.node.ASimpleOrExpr;
import src.promela.node.AStmntStep;
import src.promela.node.PAndExpr;
import src.promela.node.PBitorExpr;
import src.promela.node.POptions;
import src.promela.node.POrExpr;
import src.promela.node.PSequence;
import src.promela.node.PStep;

/**
 * Normaliser is an extention of DepthFirstAdapter which converts an AST for a
 * Promela program into "normal" form on application. This normal form allows
 * two Promela programs to be compared for equality "up to commutativity".
 * Basically the class normalises if :: ... :: fi and do :: ... :: od statements
 * so that the guards are arranged in alphabetical order. Under the assumption
 * that the init process has the form init { atomic { run p1( ); run p2(); ...
 * run pn(); } }, and that there are less than 256 such statements (and no
 * dynamic process creation in the model), run statements are also sorted.
 * 
 * The class has public access so that it is visible to classes in other
 * packages. There are no instance variables.
 * 
 * Versions: 1.0: 13/09/04: Wrote code. 1.1: 16/09/04: Commented code.
 * 
 * @author Alastair Donaldson
 * @version 1.1 (16/09/04)
 * @since 1.0 (13/09/04)
 */
public class Normaliser extends DepthFirstAdapter {

	private int noProcesses;
	
	public Normaliser(int noProcesses) {
		this.noProcesses = noProcesses;
	}
	
	/**
	 * Sorts guards of an if or do statement into alphabetical order.
	 * 
	 * @param node
	 *            AST node representing a list of guards for an if or do
	 *            statement.
	 */
	public void outANormalOptions(ANormalOptions node) {

		if (!(node.parent() instanceof ANormalOptions)) {
			// We only want to sort if we have the root of a
			// list of options.

			List<PSequence> optionList = new ArrayList<PSequence>();
			POptions temp = node;

			do {
				optionList.add(((ANormalOptions) temp).getSequence());
				temp = ((ANormalOptions) temp).getOptions();
			} while (temp != null);

			Collections.sort(optionList, new NodeComparator());

			temp = node;
			for (int i = 0; i < optionList.size(); i++) {
				((ANormalOptions) temp).setSequence((PSequence) optionList.get(i));
				temp = ((ANormalOptions) temp).getOptions();
			}
		}
	}

	/**
	 * Sorts statements in the atomic block of the init process which come AFTER the
	 * run statements into alphabetical order.  Statements must be non blocking and 
	 * commutative -- this is currently not checked.
	 * 
	 * @param node
	 *            AST node representing an init { } process.
	 */
	public void outAInit(AInit node) {

		Assert.assertFalse(node.getSequence() instanceof ANullSequence);
		
		PSequence atomicBlock = (node.getSequence() instanceof AOneSequence ? 
				((AAtomicStmnt)((AStmntStep)((AOneSequence)node.getSequence()).getStep()).getStmnt()).getSequence() :
				((AAtomicStmnt)((AStmntStep)((AManySequence)node.getSequence()).getStep()).getStmnt()).getSequence());

		PSequence statementsAfterRunStatements = findStatementsAfterRunStatement(atomicBlock);

		List<PStep> statementsList = getListOfStatements(statementsAfterRunStatements);
		Collections.sort(statementsList, new NodeComparator());
		replaceStatements(statementsAfterRunStatements, statementsList);

	}

	private List<PStep> getListOfStatements(PSequence statementsAfterRunStatements) {
		List<PStep> result = new ArrayList<PStep>();
		PSequence temp;
		for(temp = statementsAfterRunStatements; temp instanceof AManySequence; temp = ((AManySequence)temp).getSequence()) {
			result.add(((AManySequence)temp).getStep());
		}
		if(temp instanceof AOneSequence) {
			result.add(((AOneSequence)temp).getStep());
		}
		return result;
	}

	private PSequence findStatementsAfterRunStatement(PSequence atomicBlock) {
		PSequence result = atomicBlock;
		
		// There is no run statement for the init process, which is why
		// we loop to noProcesses-1
		for(int i=0; i<noProcesses-1; i++) {
			if(result instanceof AManySequence) {
				result = ((AManySequence)result).getSequence();
			} else {
				Assert.assertEquals(i,noProcesses-2);
			}
		}
		return result;
	}

	private void replaceStatements(PSequence statementsAfterRunStatements, List<PStep> newStatements) {
		PSequence temp = statementsAfterRunStatements;
		for(int i=0; i<newStatements.size(); i++) {
			if(temp instanceof AManySequence) {
				((AManySequence)temp).setStep(newStatements.get(i));
				temp = ((AManySequence)temp).getSequence();
			} else {
				((AOneSequence)temp).setStep(newStatements.get(i));
			}
		}

	}

	public void outACompoundOrExpr(ACompoundOrExpr node) {
		if (!(node.parent() instanceof POrExpr)) {

			List<PAndExpr> operands = new ArrayList<PAndExpr>();

			// BUILD UP LIST OF OPERANDS
			POrExpr temp = node;

			int i = 0;

			while (temp instanceof ACompoundOrExpr) {
				operands.add(i,((ACompoundOrExpr)temp).getAndExpr());

				i++;
				temp = ((ACompoundOrExpr) temp).getOrExpr();
			}

			operands.add(i, ((ASimpleOrExpr) temp).getAndExpr());

			// SORT LIST OF OPERANDS
			Collections.sort(operands, new NodeComparator());

			// REPLACE OPERANDS IN SORTED ORDER
			temp = node;
			i = 0;
			while (temp instanceof ACompoundOrExpr) {
				((ACompoundOrExpr) temp).setAndExpr((PAndExpr) operands.get(i));
				i++;
				temp = ((ACompoundOrExpr) temp).getOrExpr();
			}

			((ASimpleOrExpr) temp).setAndExpr((PAndExpr) operands.get(i));

		}
	}

	public void outACompoundAndExpr(ACompoundAndExpr node) {
		if (!(node.parent() instanceof PAndExpr)) {

			List<PBitorExpr> operands = new ArrayList<PBitorExpr>();

			// BUILD UP LIST OF OPERANDS
			PAndExpr temp = node;

			int i = 0;

			while (temp instanceof ACompoundAndExpr) {
				operands.add(i, ((ACompoundAndExpr) temp).getBitorExpr());

				i++;
				temp = ((ACompoundAndExpr) temp).getAndExpr();
			}

			operands.add(i, ((ASimpleAndExpr) temp).getBitorExpr());

			// SORT LIST OF OPERANDS
			Collections.sort(operands, new NodeComparator());

			// REPLACE OPERANDS IN SORTED ORDER
			temp = node;
			i = 0;
			while (temp instanceof ACompoundAndExpr) {
				((ACompoundAndExpr) temp).setBitorExpr((PBitorExpr) operands
						.get(i));
				i++;
				temp = ((ACompoundAndExpr) temp).getAndExpr();
			}

			((ASimpleAndExpr) temp).setBitorExpr((PBitorExpr) operands.get(i));

		}
	}

}
