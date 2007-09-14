package src.etch.checker;

import junit.framework.Assert;
import src.etch.error.BadlyFormedInitError;
import src.promela.node.AAtomicCompoundStmnt;
import src.promela.node.ACompoundStmnt;
import src.promela.node.ACompoundUnseparatedStep;
import src.promela.node.AExpressionSimpleStmnt;
import src.promela.node.AInit;
import src.promela.node.AInitModule;
import src.promela.node.AManySequence;
import src.promela.node.AOneSequence;
import src.promela.node.ARunFactor;
import src.promela.node.ASimpleAddExpr;
import src.promela.node.ASimpleAndExpr;
import src.promela.node.ASimpleBitandExpr;
import src.promela.node.ASimpleBitorExpr;
import src.promela.node.ASimpleBitxorExpr;
import src.promela.node.ASimpleEqExpr;
import src.promela.node.ASimpleExpr;
import src.promela.node.ASimpleMultExpr;
import src.promela.node.ASimpleOrExpr;
import src.promela.node.ASimpleRelExpr;
import src.promela.node.ASimpleShiftExpr;
import src.promela.node.ASimpleStmnt;
import src.promela.node.ASimpleUnExpr;
import src.promela.node.AStatementStep;
import src.promela.node.PCompoundStmnt;
import src.promela.node.PSequence;
import src.promela.node.PStep;
import src.promela.node.PStmnt;

public class SymmetrySettings {
	
	/* If we are type checking before symmetry reduction then the
	 * number of processes in the specification is vital, as this
	 * defines the literal range for the `pid' type
	 */
	protected static int noProcesses;
	
	/* Records whether or not we are type checking before symmetry
	 * reduction
	 */
	public static boolean CHECKING_SYMMETRY = false;
		
	public static void setNoProcesses(int noProcesses) {
		SymmetrySettings.noProcesses = noProcesses;
	}

	public static int noProcesses() {
		return noProcesses;
	}
	
	protected static void findNumberOfRunningProcesses(AInitModule module, Checker checker) {

		AInit init = (AInit) module.getInit();
		
		if(!isAtomicStatement(init.getSequence())) {
			checker.addError(init.getInittok(),new BadlyFormedInitError());
			noProcesses = 0; return;
		}

		int result = 0;
		PSequence statementsWithinAtomic;
		
		statementsWithinAtomic = getStatementsWithinAtomic(init);

		for( ; statementsWithinAtomic instanceof AManySequence; statementsWithinAtomic = nextInSequence(statementsWithinAtomic)) {
			
			if(!isRunStatement(((AManySequence)statementsWithinAtomic).getStep())) {
				if(result==0) {
					checker.addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
				}
				noProcesses = result;
				return;
			} else {
				result++;
				// We used to do setOut(getRunStatement(     ), new PidType);
				// However, this doesn't seem necessary.
			}
		}

		Assert.assertTrue(statementsWithinAtomic instanceof AOneSequence);

		if(!isRunStatement(((AOneSequence)statementsWithinAtomic).getStep())) {
			if(result==0) {
				checker.addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
			}
			noProcesses = result;
		} else {
			result++;
			// We used to do setOut(getRunStatement(     ), new PidType);
			// However, this doesn't seem necessary.
		}
		
		/* TODO Check that any other statements within the init block are commutative */
	}

	public static PSequence getStatementsWithinAtomic(AInit init) {
		PSequence statementsWithinAtomic;
		PSequence initSequence = init.getSequence();
		PStep firstStepInInitSequence;

		if(initSequence instanceof AOneSequence) {
			firstStepInInitSequence = ((AOneSequence)initSequence).getStep();
		} else {
			firstStepInInitSequence = ((AManySequence)initSequence).getStep();
		}
		
		Assert.assertTrue(firstStepInInitSequence instanceof AStatementStep || firstStepInInitSequence instanceof ACompoundUnseparatedStep);

		PCompoundStmnt atomicCompoundStatement;
		
		if(firstStepInInitSequence instanceof AStatementStep) {
			PStmnt atomicStatement = ((AStatementStep)firstStepInInitSequence).getStmnt();
			Assert.assertTrue(atomicStatement instanceof ACompoundStmnt);
			atomicCompoundStatement = ((ACompoundStmnt)atomicStatement).getCompoundStmnt();
		} else {
			atomicCompoundStatement = ((ACompoundUnseparatedStep)firstStepInInitSequence).getCompoundStmnt();
		}

		Assert.assertTrue(atomicCompoundStatement instanceof AAtomicCompoundStmnt);
		statementsWithinAtomic = ((AAtomicCompoundStmnt)atomicCompoundStatement).getSequence();
		return statementsWithinAtomic;
	}

	private static PSequence nextInSequence(PSequence seq) {
		Assert.assertTrue(seq instanceof AManySequence);
		return ((AManySequence)seq).getSequence();
	}

	private static boolean isAtomicStatement(PSequence sequence) {
		return sequence.toString().length()>=7 && sequence.toString().substring(0,7).equals("atomic ");
	}

	private ARunFactor getRunStatement(PStep step) {
		Assert.assertTrue(isRunStatement(step));
		return (ARunFactor)((ASimpleUnExpr)((ASimpleMultExpr)((ASimpleAddExpr)((ASimpleShiftExpr)((ASimpleRelExpr)((ASimpleEqExpr)((ASimpleBitandExpr)((ASimpleBitxorExpr)
				((ASimpleBitorExpr)((ASimpleAndExpr)((ASimpleOrExpr)((ASimpleExpr)((AExpressionSimpleStmnt)(((ASimpleStmnt)((AStatementStep)step).getStmnt()).getSimpleStmnt())).getExpr()).getOrExpr())
				.getAndExpr()).getBitorExpr()).getBitxorExpr()).getBitandExpr()).getEqExpr()).getRelExpr())
				.getShiftExpr()).getAddExpr()).getMultExpr()).getUnExpr()).getFactor();
	}

	private static boolean isRunStatement(PStep step) {
		return step.toString().substring(0,4).equals("run ");
	}

}
