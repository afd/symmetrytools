package src.symmextractor;


import src.etch.checker.Checker;
import src.etch.env.ProctypeEntry;
import src.etch.typeinference.ConstraintSet;
import src.etch.types.ArrayType;
import src.etch.types.Type;
import src.etch.types.VisibleType;
import src.promela.NodeHelper;
import src.promela.node.AArrayIvar;
import src.promela.node.AArrayref;
import src.promela.node.AAtomicCompoundStmnt;
import src.promela.node.AChannelIvarassignment;
import src.promela.node.ACompoundShiftExpr;
import src.promela.node.ACompoundStmnt;
import src.promela.node.ACompoundUnseparatedStep;
import src.promela.node.AInit;
import src.promela.node.AInitModule;
import src.promela.node.AManyActive;
import src.promela.node.AManyModules;
import src.promela.node.AManySequence;
import src.promela.node.ANormalSpec;
import src.promela.node.ANotUnExpr;
import src.promela.node.AOneActive;
import src.promela.node.AOneModules;
import src.promela.node.AOneSequence;
import src.promela.node.APidConst;
import src.promela.node.APidTypename;
import src.promela.node.AProctype;
import src.promela.node.ARecordVarref;
import src.promela.node.ARunFactor;
import src.promela.node.ASingleIvar;
import src.promela.node.ASingleVarref;
import src.promela.node.AStatementStep;
import src.promela.node.Node;
import src.promela.node.PCompoundStmnt;
import src.promela.node.PIvar;
import src.promela.node.PModule;
import src.promela.node.PModules;
import src.promela.node.PSequence;
import src.promela.node.PStep;
import src.promela.node.PStmnt;
import src.promela.node.PVarref;
import src.promela.node.TActivetok;
import src.promela.node.Token;
import src.symmextractor.error.ActiveProctypeError;
import src.symmextractor.error.BadlyFormedInitError;
import src.symmextractor.error.DynamicChannelCreationError;
import src.symmextractor.error.DynamicProcessCreationError;
import src.symmextractor.error.GlobalArrayOfChannelsError;
import src.symmextractor.error.NoInitError;
import src.symmextractor.error.PidIndexedArrayWithWrongLengthError;
import src.symmextractor.types.PidLiteralCandidate;
import src.symmextractor.types.PidType;
import src.symmextractor.types.SymmExtractorTypeFactory;

public class SymmetryChecker extends Checker {

	private String currentProctypeName;

	private boolean inProctype = false;

	private int numberOfLinesInSourceFile;

	private static int noProcesses;

	public SymmetryChecker(int numberOfLinesInSourceFile) {
		Checker.theFactory = new SymmExtractorTypeFactory();
		constraintSet = new ConstraintSet(new PidSensitiveUnifier());
		this.numberOfLinesInSourceFile = numberOfLinesInSourceFile;
	}
	
	public void caseAProctype(AProctype node) {

		inProctype = true;

		if(node.getActive()!=null) {
			addError(getActiveToken(node), new ActiveProctypeError(node.getName().getText()));
		}

		currentProctypeName = node.getName().getText();
		super.caseAProctype(node);
		inProctype = false;

	}	

	public void outAChannelIvarassignment(AChannelIvarassignment node) {

		if(inTypedef) {
			addError(node.getAssign(), new DynamicChannelCreationError(nameOfAssociatedChannel(node), true));
		}
		
		if(inProctype) {
			addError(node.getAssign(), new DynamicChannelCreationError(nameOfAssociatedChannel(node), false));
		}
		
		PIvar channel = (PIvar) node.parent();

		if (channel instanceof AArrayIvar) {
			addError(node.getLBracket(), new GlobalArrayOfChannelsError( ((AArrayIvar)channel).getName().getText()));
		}
	}

	private String nameOfAssociatedChannel(AChannelIvarassignment node) {
		if(node.parent() instanceof ASingleIvar) {
			return ((ASingleIvar)node.parent()).getName().getText();
		} else {
			return ((AArrayIvar)node.parent()).getName().getText();
		}
	}
	
	public void caseAInit(AInit node) {
		currentProctypeName = ProctypeEntry.initProctypeName;
		super.caseAInit(node);
	}

	private TActivetok getActiveToken(AProctype node) {
		if(node.getActive() instanceof AOneActive) {
			return ((AOneActive)node.getActive()).getActivetok();
		}
		return ((AManyActive)node.getActive()).getActivetok();
	}

	public void outARunFactor(ARunFactor node) {
		super.outARunFactor(node);

		if(!currentProctype.equals(ProctypeEntry.initProctypeEntry)) {
			addError(node.getRun(), new DynamicProcessCreationError(node.getName().getText(), currentProctypeName));
		}
	}

	public void caseANormalSpec(ANormalSpec node) {

		PModules modules = node.getModules();
		
		boolean found = false;

		PModules temp = modules;
		
		for( ; temp instanceof AManyModules; temp = ((AManyModules)temp).getModules() ) {
			PModule module = ((AManyModules)temp).getModule();
			if(module instanceof AInitModule) {
				findNumberOfRunningProcesses((AInitModule)module);
				found = true;
				break;
			}
		}

		if(!found) {
			PModule module = ((AOneModules)temp).getModule();
			if(module instanceof AInitModule) {
				findNumberOfRunningProcesses((AInitModule)module);
				found = true;
			}
		}
		
		if(!found) {
			errorTable.add(numberOfLinesInSourceFile, new NoInitError());
		}

		modules.apply(this);

	}


	private void findNumberOfRunningProcesses(AInitModule module) {

		AInit init = (AInit) module.getInit();

		noProcesses = 0;

		if(!isAtomicStatement(init.getSequence())) {
			addError(init.getInittok(),new BadlyFormedInitError());
			return;
		}

		PSequence statementsWithinAtomic;
		
		statementsWithinAtomic = getStatementsWithinAtomic(init);

		for( ; statementsWithinAtomic instanceof AManySequence; statementsWithinAtomic = nextInSequence(statementsWithinAtomic)) {
			
			if(!isRunStatement(((AManySequence)statementsWithinAtomic).getStep())) {
				if(noProcesses==0) {
					addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
				}
				return;
			} else {
				noProcesses++;
				// We used to do setOut(getRunStatement(     ), new PidType);
				// However, this doesn't seem necessary.
			}
		}

		assert(statementsWithinAtomic instanceof AOneSequence);

		if(!isRunStatement(((AOneSequence)statementsWithinAtomic).getStep())) {
			if(noProcesses==0) {
				addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
			}
			return;
		} else {
			noProcesses++;
			// We used to do setOut(getRunStatement(     ), new PidType);
			// However, this doesn't seem necessary.
		}

		/* TODO Check that any other statements within the init block are commutative */

	}
	

	private static PSequence nextInSequence(PSequence seq) {
		assert(seq instanceof AManySequence);
		return ((AManySequence)seq).getSequence();
	}

	private static boolean isAtomicStatement(PSequence sequence) {
		return sequence.toString().length()>=7 && sequence.toString().substring(0,7).equals("atomic ");
	}

	private static boolean isRunStatement(PStep step) {
		return step.toString().substring(0,4).equals("run ");
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
		
		assert(firstStepInInitSequence instanceof AStatementStep || firstStepInInitSequence instanceof ACompoundUnseparatedStep);

		PCompoundStmnt atomicCompoundStatement;
		
		if(firstStepInInitSequence instanceof AStatementStep) {
			PStmnt atomicStatement = ((AStatementStep)firstStepInInitSequence).getStmnt();
			assert(atomicStatement instanceof ACompoundStmnt);
			atomicCompoundStatement = ((ACompoundStmnt)atomicStatement).getCompoundStmnt();
		} else {
			atomicCompoundStatement = ((ACompoundUnseparatedStep)firstStepInInitSequence).getCompoundStmnt();
		}

		assert(atomicCompoundStatement instanceof AAtomicCompoundStmnt);
		statementsWithinAtomic = ((AAtomicCompoundStmnt)atomicCompoundStatement).getSequence();
		return statementsWithinAtomic;
	}
	
	private Type getArrayIndexType(PVarref node) {
		if(node instanceof ASingleVarref) {
			return getOutType(((AArrayref) ((ASingleVarref)node).getArrayref()).getExpr());
		}
		return getOutType(((AArrayref) ((ARecordVarref)node).getArrayref()).getExpr());
	}

	protected void dealWithArrayIndex(PVarref node, VisibleType t) {
		if (getArrayIndexType(node) != null) {
			if(getArrayIndexType(node) instanceof PidType && ((ArrayType)t).getLength()!=(noProcesses+1) && ((ArrayType)t).getLength()!=0) {
				// The length of a pid-indexed array should be n+1, where n is the number of running processes.
				// This is so that it can be indexed by the process identifiers 1, 2, ... , n.  Unfortunately, index
				// 0 is usually wasted (unless the init process uses it).
				// We don't add an error if the length is zero.  An error has either already
				// been reported about this, or the length has been set to zero by default as
				// there was an error with the initialiser.
				addError(NodeHelper.getNameFromVaribableReference(node), new PidIndexedArrayWithWrongLengthError(NodeHelper.getNameFromVaribableReference(node).getText(),((ArrayType)t).getLength(),noProcesses));
				((ArrayType)t).zeroLength(); // Do this so that the error will not be reported again
			}
			postSubtypingConstraint(getArrayIndexType(node), ((ArrayType) t)
					.getIndexType(), NodeHelper.getNameFromVaribableReference(node));
		}
	}
	
	public void outAPidTypename(APidTypename node) {
		setOut(node, new PidType());
	}
	
	protected boolean suitableTypeForArrayIndex(Type exprType) {
		return super.suitableTypeForArrayIndex(exprType) || exprType.isSubtype(new PidType());
	}
	
	public void outAPidConst(APidConst node) {
		setOut(node, new PidType());
	}

	public static int numberOfRunningProcesses() {
		return noProcesses;
	}

	public void outACompoundShiftExpr(ACompoundShiftExpr node) {
		super.outACompoundShiftExpr(node);
		if(getOut(node) instanceof VisibleType) {
			setNotPidLiteral((VisibleType)getOut(node));
		}
	}

	public void outANotUnExpr(ANotUnExpr node) {
		super.outANotUnExpr(node);
		if(getOut(node) instanceof VisibleType) {
			setNotPidLiteral((VisibleType)getOut(node));
		}
	}
	
	protected void checkNumericOperationOnNumericTypes(Node node,
			Token operation, VisibleType leftType, VisibleType rightType) {
		super.checkNumericOperationOnNumericTypes(node, operation, leftType, rightType);
		if (getOut(node) instanceof Type) {
			setNotPidLiteral((Type)getOut(node));
		}
	}

	public static void setNotPidLiteral(Type t) {
		if(t instanceof PidLiteralCandidate) {
			((PidLiteralCandidate)t).setNotPidLiteral();
		}
	}
	
	
}

