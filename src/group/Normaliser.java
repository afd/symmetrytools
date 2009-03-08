package src.group;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import src.advice.LocationReferenceCollector;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AAssignSimpleStmnt;
import src.promela.node.AAssignmentAssignment;
import src.promela.node.AAtomicCompoundStmnt;
import src.promela.node.ACompoundAndExpr;
import src.promela.node.ACompoundOrExpr;
import src.promela.node.ACompoundStmnt;
import src.promela.node.ACompoundUnseparatedStep;
import src.promela.node.ADecrementAssignment;
import src.promela.node.ADstepCompoundStmnt;
import src.promela.node.AIncrementAssignment;
import src.promela.node.AInit;
import src.promela.node.AManySequence;
import src.promela.node.ANormalOptions;
import src.promela.node.AOneSequence;
import src.promela.node.ASimpleAndExpr;
import src.promela.node.ASimpleOrExpr;
import src.promela.node.ASimpleStmnt;
import src.promela.node.AStatementStep;
import src.promela.node.Node;
import src.promela.node.PAndExpr;
import src.promela.node.PAssignment;
import src.promela.node.PBitorExpr;
import src.promela.node.POptions;
import src.promela.node.POrExpr;
import src.promela.node.PSequence;
import src.promela.node.PStep;
import src.symmextractor.SymmetryChecker;

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

	private int atomicityLevel = 0;
	
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
	
	public void inAAtomicCompoundStmnt(AAtomicCompoundStmnt node) {
		atomicityLevel++;
	}

	public void inADstepCompoundStmnt(ADstepCompoundStmnt node) {
		atomicityLevel++;
	}

	public void outAAtomicCompoundStmnt(AAtomicCompoundStmnt node) {
		atomicityLevel--;
	}

	public void outADstepCompoundStmnt(ADstepCompoundStmnt node) {
		atomicityLevel--;
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

		PSequence atomicBlock = SymmetryChecker.getStatementsWithinAtomic(node);

		PSequence statementsAfterRunStatements = findStatementsAfterRunStatement(atomicBlock);

		List<PStep> statementsList = getListOfStatements(statementsAfterRunStatements);
		Collections.sort(statementsList, new NodeComparator());
		replaceStatements(statementsAfterRunStatements, statementsList);

	}

	private List<PStep> getListOfStatements(PSequence statementsAfterRunStatements) {
		List<PStep> result = new ArrayList<PStep>();
		PSequence temp = statementsAfterRunStatements;
		for(; temp instanceof AManySequence; temp = ((AManySequence)temp).getSequence()) {
			addStep(result, ((AManySequence)temp).getStep());
		}
		assert(temp instanceof AOneSequence);
		addStep(result,((AOneSequence)temp).getStep());
		return result;
	}

	private void addStep(List<PStep> result, PStep step) {
		if(step instanceof ACompoundUnseparatedStep) {
			result.add(new AStatementStep(new ACompoundStmnt(((ACompoundUnseparatedStep)step).getCompoundStmnt())));
			result.add(((ACompoundUnseparatedStep)step).getStep());
		} else {
			result.add(step);
		}
	}

	private PSequence findStatementsAfterRunStatement(PSequence atomicBlock) {
		PSequence result = atomicBlock;
		
		/* I feel quite suspicious of this method.  Does it cope OK with:
		 *
		 * init { atomic {
		 *    run ...;
		 *    run ...;
		 *    run ...;
		 * } }
		 * 
		 * i.e. the case where there are no additional statements?
		 * 
		 */
		
		// There is no run statement for the init process, which is why
		// we loop to noProcesses-1
		for(int i=0; i<noProcesses-1; i++) {
			if(result instanceof AManySequence) {
				result = ((AManySequence)result).getSequence();
			} else {
				assert(i == noProcesses-2);
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
	
	
	
	
	private boolean interchangeable(PAssignment s1, PAssignment s2) {
		
		Set<String> writtenLocationsS1 = getWrittenLocations(s1);
		Set<String> writtenLocationsS2 = getWrittenLocations(s2);
		Set<String> readLocationsS1 = getReadLocations(s2);
		Set<String> readLocationsS2 = getReadLocations(s2);
				
		boolean result = locationSetsDisjoint(writtenLocationsS1, writtenLocationsS2)
		   && locationSetsDisjoint(writtenLocationsS1, readLocationsS2)
		   && locationSetsDisjoint(writtenLocationsS2, readLocationsS1);
				
		return result;
		
	}

	private boolean locationSetsDisjoint(Set<String> locations1, Set<String> locations2) {
		
		for(String location1 : locations1) {
			for(String location2 : locations2) {
				if(locationsOverlap(location1, location2)) {
					return false;
				}
			}
		}
		return true;
		
	}

	private boolean locationsOverlap(String location1, String location2) {
		String location1WithoutIndices = removeIndices(location1);
		String location2WithoutIndices = removeIndices(location2);
		
		if(!location1WithoutIndices.equals(location2WithoutIndices)) {
			return false;
		}
		
		List<String> location1Indices = getIndices(location1);
		List<String> location2Indices = getIndices(location2);
		
		for(int i=0; i< location1Indices.size(); i++) {
			
			if ( !( location1Indices.get(i).equals("#") || location2Indices.get(i).equals("#"))) {
				
				if ( ! location1Indices.get(i).equals(location2Indices.get(i) ) ) {
					return false;
				}
				
			}
		}
		
		return true;
		

	}

	private List<String> getIndices(String s) {
		List<String> result = new ArrayList<String>();

		boolean inArrayIndex = false;
		
		String currentArrayIndex = null;
		
		for(int index = 0; index < s.length(); index++)
		{
			if(s.charAt(index)==']') {
				result.add(currentArrayIndex);
				inArrayIndex = false;
			}
			
			if(inArrayIndex) {
				currentArrayIndex += s.charAt(index);
			}
			
			if(s.charAt(index)=='[') {
				inArrayIndex = true;
				currentArrayIndex = new String("");
			}
		}
		
		return result;

	}

	private String removeIndices(String s) {
		String result = "";
		boolean inArrayIndex = false;
		
		for(int index = 0; index < s.length(); index++)
		{
			if(!inArrayIndex) {
				result += s.charAt(index);
			}
			
			if(s.charAt(index)=='[') {
				inArrayIndex = true;
			}
			
			if(s.charAt(index)==']') {
				inArrayIndex = false;
				result += ']';
			}

		}
		
		return result;
	}

	private Set<String> getReadLocations(PAssignment s) {
		if(s instanceof AIncrementAssignment) {
			return getReferencedLocations(((AIncrementAssignment)s).getVarref());
		}

		if(s instanceof ADecrementAssignment) {
			return getReferencedLocations(((ADecrementAssignment)s).getVarref());
		}
		
		return getReferencedLocations(((AAssignmentAssignment)s).getOrExpr());
	}

	private Set<String> getWrittenLocations(PAssignment s) {
		if(s instanceof AIncrementAssignment) {
			return getReferencedLocations(((AIncrementAssignment)s).getVarref());
		}

		if(s instanceof ADecrementAssignment) {
			return getReferencedLocations(((ADecrementAssignment)s).getVarref());
		}
		
		return getReferencedLocations(((AAssignmentAssignment)s).getVarref());
	}
	
	private Set<String> getReferencedLocations(Node node) {
		LocationReferenceCollector collector = new LocationReferenceCollector();
		node.apply(collector);
		return collector.getReferences();
	}
	
	public void caseAManySequence(AManySequence node) {
		
		// Fist, normalize the sequence
		
		PSequence temp = node;
		while(temp instanceof AManySequence) {
			((AManySequence)temp).getStep().apply(this);
			temp = ((AManySequence)temp).getSequence();
		}
		((AOneSequence)temp).getStep().apply(this);
		
		/* Only try sequence rearrangement if in atomic block */
		if(0 == atomicityLevel) {
			return;
		}
		
		PSequence tentativeCurrentBlock = skipToFirstAssignment(node);
		
		if(null == tentativeCurrentBlock || tentativeCurrentBlock instanceof AOneSequence) {
			return;
		}
		
		AManySequence currentBlock = (AManySequence)tentativeCurrentBlock;
		
		PSequence tail = currentBlock.getSequence();
				
		int currentBlockSize = 1;
		
		for(;;) {
			
			if(nextStepIsIndependentAssignment(tail, currentBlock, currentBlockSize)) {

				currentBlockSize++;
				
				if(tail instanceof AManySequence) {
					tail = ((AManySequence)tail).getSequence();
				} else {
					tail = null;
				}
				
			} else {
				
				
				sortBlock(currentBlock, currentBlockSize);
				
				tentativeCurrentBlock = skipToFirstAssignment(tail);
				if(null == tentativeCurrentBlock || tentativeCurrentBlock instanceof AOneSequence) {
					return;
				}
				
				currentBlock = (AManySequence)tentativeCurrentBlock;
				
				tail = ((AManySequence)currentBlock).getSequence();
				
				currentBlockSize = 1;

			}
			
			
		}
				
	}

	private void sortBlock(AManySequence currentBlock, int currentBlockSize) {
		
		List<PStep> stepList = getListOfStepsForBlock(currentBlock, currentBlockSize);
				
		Collections.sort(stepList, new NodeComparator());
		
		replaceListOfStepsInBlock(currentBlock, currentBlockSize, stepList);
		
	}

	private void replaceListOfStepsInBlock(AManySequence currentBlock, int currentBlockSize, List<PStep> stepList) {
		PSequence temp = currentBlock;
		
		for(int i = 0; i < currentBlockSize; i++) {
			if ( temp instanceof AManySequence ) {
				((AManySequence)temp).setStep(stepList.get(i));;
				temp = ((AManySequence)temp).getSequence();
			} else {
				((AOneSequence)temp).setStep(stepList.get(i));;
				assert(currentBlockSize-1 == i);
			}
		}
	}

	private List<PStep> getListOfStepsForBlock(AManySequence currentBlock, int currentBlockSize) {
		List<PStep> result = new ArrayList<PStep>();
		PSequence temp = currentBlock;
		for(int i = 0; i < currentBlockSize; i++) {
			if ( temp instanceof AManySequence ) {
				result.add(((AManySequence)temp).getStep());
				temp = ((AManySequence)temp).getSequence();
			} else {
				result.add(((AOneSequence)temp).getStep());
				assert(currentBlockSize-1 == i);
			}
		}
		
		return result;
	}

	private boolean nextStepIsIndependentAssignment(PSequence tail, AManySequence currentBlock, final int currentBlockSize) {

		assert ( isAssignmentStep(currentBlock.getStep()));
		
		if(null == tail) {
			return false;
		}
		
		PAssignment nextAssignment;
		
		if(tail instanceof AOneSequence) {
			if(!isAssignmentStep(((AOneSequence)tail).getStep())) {
				return false;
			}
		} else {
			if(!isAssignmentStep(((AManySequence)tail).getStep())) {
				return false;
			}
		}
		
		nextAssignment = extractAssignmentStatement(tail);
		
		AManySequence nextInBlock = currentBlock;
		
		for(int i = 0; i < currentBlockSize; i++) {
			
			if(!interchangeable(nextAssignment, extractAssignmentStatement(nextInBlock))) {
				return false;
			}
						
			if( i < currentBlockSize - 1) {
				nextInBlock = (AManySequence)currentBlock.getSequence();
			}
		}
		
		return true;
		
	}

	private PAssignment extractAssignmentStatement(PSequence tail) {
		PStep step;
		if(tail instanceof AOneSequence) {
			step = ((AOneSequence)tail).getStep();
		} else {
			 step = ((AManySequence)tail).getStep();
		}
		return ((AAssignSimpleStmnt)((ASimpleStmnt)((AStatementStep)step).getStmnt()).getSimpleStmnt()).getAssignment();
	}

	private PSequence skipToFirstAssignment(PSequence seq) {
		if(null == seq) {
			return null;
		}
		
		while(seq instanceof AManySequence) {
			if(isAssignmentStep(((AManySequence)seq).getStep())) {
				return seq;
			}
			seq = ((AManySequence)seq).getSequence();
		}
		
		if(isAssignmentStep(((AOneSequence)seq).getStep())) {
			return seq;
		}
		
		return null;
	}

	private boolean isAssignmentStep(PStep step) {
		return (step instanceof AStatementStep) && ( ((AStatementStep)step).getStmnt() instanceof ASimpleStmnt)
		&& ( ((ASimpleStmnt)((AStatementStep)step).getStmnt()).getSimpleStmnt() instanceof AAssignSimpleStmnt );
	}
}
