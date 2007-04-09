package src.etch.checker;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import src.etch.env.ChannelEntry;
import src.etch.env.Env;
import src.etch.env.EnvEntry;
import src.etch.env.MtypeEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.TypeEntry;
import src.etch.env.VarEntry;
import src.etch.error.ArithmeticOnPidError;
import src.etch.error.ArrayWithLengthZeroError;
import src.etch.error.AssignmentMismatchError;
import src.etch.error.BadlyFormedInitError;
import src.etch.error.ElementDoesNotExistError;
import src.etch.error.EqMismatchError;
import src.etch.error.Error;
import src.etch.error.ErrorTable;
import src.etch.error.IfCondError;
import src.etch.error.IfMismatchError;
import src.etch.error.LiteralValueTooLargeError;
import src.etch.error.NameAlreadyUsedError;
import src.etch.error.NoInitError;
import src.etch.error.NotBoolError;
import src.etch.error.NotNumericError;
import src.etch.error.PidIndexedArrayWithWrongLengthError;
import src.etch.error.SubtypingError;
import src.etch.error.VariableNotArrayError;
import src.etch.error.VariableNotChannelError;
import src.etch.error.VariableNotRecordError;
import src.etch.error.WrongNumArgsError;
import src.etch.types.ArrayType;
import src.etch.types.BitType;
import src.etch.types.BoolType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.IncomparableTypesException;
import src.etch.types.IntType;
import src.etch.types.MtypeType;
import src.etch.types.NumericType;
import src.etch.types.PidType;
import src.etch.types.RecordType;
import src.etch.types.ShortType;
import src.etch.types.Type;
import src.etch.types.TypeVariableFactory;
import src.etch.types.TypeVariableType;
import src.etch.unifier.ConstraintSet;
import src.etch.unifier.EqualityConstraint;
import src.etch.unifier.Substituter;
import src.etch.unifier.SubtypingConstraint;
import src.promela.node.*;

public class Checker extends InlineProcessor {
	
	private ErrorTable errorTable = new ErrorTable();

	private Env env = new Env();

	private ConstraintSet constraintSet = new ConstraintSet();

	private TypeVariableFactory factory = new TypeVariableFactory('X');

	protected boolean inTypedef = false;

	private List<String> callStack = new ArrayList<String>();
	
	private static final String USER_TYPE = "user defined type";
	private static final String PROCTYPE = "proctype";
	private static final String VARIABLE = "variable";
	private static final String FIELD = "field";
	
	protected ProctypeEntry currentProctype = null;

	private List<String> typedefFieldNames = new ArrayList<String>();

	private List<Type> typedefFieldTypes = new ArrayList<Type>();

	public void caseANormalSpec(ANormalSpec node) {
		
		if(Type.checkingSymmetry()) {

			boolean found = false;
			for(Object module : node.getModule()) {

				if(module instanceof AInitModule) {

					Type.setNoProcesses(findNumberOfRunningProcesses((AInitModule)module));
					found = true;
					break;

				}
			}
			if(!found) {
				errorTable.add(-1,new NoInitError());
			}
		}
	
		for(Object module : node.getModule()) {
			((Node)module).apply(this);
		}

	}
	
	private int findNumberOfRunningProcesses(AInitModule module) {
		
		PSequence initsequence = ((AInit) module.getInit()).getSequence();
		if(initsequence instanceof ANullSequence) {
			// ERROR : Form of init process
			return 0;
		}
		PStep initFirstStep;
		if(initsequence instanceof AOneSequence) {
			initFirstStep = ((AOneSequence)initsequence).getStep();
		} else {
			initFirstStep = ((AManySequence)initsequence).getStep();
		}


		if(!isAtomicStatement(initFirstStep)) {

			addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
			return 0;
		}

		int result = 0;
		
		PSequence atomicSequence;
		
		for(atomicSequence = ((AAtomicStmnt)((AStmntStep)initFirstStep).getStmnt()).getSequence();
atomicSequence instanceof AManySequence; atomicSequence = ((AManySequence)atomicSequence).getSequence()) {
			
			if(!isRunStatement(((AManySequence)atomicSequence).getStep())) {
				if(result==0) {
					addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
				}
				return result;
			} else {
				result++;
				setOut(getRunStatement(((AManySequence)atomicSequence).getStep()),new PidType());
			}
		}
		
		if(atomicSequence instanceof AOneSequence && isRunStatement(((AOneSequence)atomicSequence).getStep())) {
			result++;
			setOut(getRunStatement(((AOneSequence)atomicSequence).getStep()),new PidType());
		}

		if(result==0) {
			addError(((AInit)module.getInit()).getInittok(),new BadlyFormedInitError());
		}
		return result;

		/* TODO Check that any other statements within the init block are commutative */
		
	}

	private boolean isRunStatement(PStep step) {
		return step.toString().substring(0,4).equals("run ");
	}

	private ARunFactor getRunStatement(PStep step) {
		Assert.assertTrue(isRunStatement(step));
		return (ARunFactor)((ASimpleUnExpr)((ASimpleMultExpr)((ASimpleAddExpr)((ASimpleShiftExpr)((ASimpleRelExpr)((ASimpleEqExpr)((ASimpleBitandExpr)((ASimpleBitxorExpr)
				((ASimpleBitorExpr)((ASimpleAndExpr)((ASimpleOrExpr)((ASimpleExpr)((AExpressionStmnt)((AStmntStep)step).getStmnt()).getExpr()).getOrExpr())
				.getAndExpr()).getBitorExpr()).getBitxorExpr()).getBitandExpr()).getEqExpr()).getRelExpr())
				.getShiftExpr()).getAddExpr()).getMultExpr()).getUnExpr()).getFactor();
	}

	private boolean isAtomicStatement(PStep step) {
		return step.toString().length()>=7 && step.toString().substring(0,7).equals("atomic ");
	}

	public Checker(boolean checkingSymmetry) {
		NumericType.setCheckingSymmetry(checkingSymmetry);
	}

	public ErrorTable getErrorTable() {
		return errorTable;
	}

	public EnvEntry getEnvEntry(String name) {
		return env.get(name);
	}

	protected void putEnvEntry(String name, EnvEntry entry) {
		env.put(name,entry);
	}
	
	public Env getEnv() {
		return env;
	}
	
	public Substituter unify() {
		return constraintSet.unify(errorTable);
	}

	public void caseAMtype(AMtype node) {
		PNameLst names = node.getNameLst();
		while (names instanceof AManyNameLst) {
			addMtypeNameToEnvironment(((AManyNameLst) names).getName()
					.getText(), node.getMtypetok());
			names = ((AManyNameLst) names).getNameLst();
		}
		addMtypeNameToEnvironment(((AOneNameLst) names).getName().getText(),
				node.getMtypetok());
	}

	private void addMtypeNameToEnvironment(String name, Token tok) {
		if (nameExists(name)) {
			addError(tok, new NameAlreadyUsedError(name,env.get(name)));
		} else {
			env.put(name, new MtypeEntry());
		}
	}

	private boolean nameExists(String name) {
		return env.get(name) != null;
	}
	
	public void caseAUtype(AUtype node) {
		enterTypedef();

		node.getDeclLst().apply(this);
		String name = node.getName().getText();

		EnvEntry alreadyExists = env.putGlobal(name, new TypeEntry(typedefFieldNames, typedefFieldTypes));
		if(alreadyExists != null) {
			addError(node.getName(), new NameAlreadyUsedError(name,alreadyExists));
		}

		exitTypedef();
	}

	public void outAOneDecl(AOneDecl node) {
		PIvarLst variables = node.getIvarLst();
		while (variables instanceof AManyIvarLst) {
			processVar(((AManyIvarLst) variables).getIvar(), getOutType(node
					.getTypename()),isHidden(node));
			variables = ((AManyIvarLst) variables).getIvarLst();
		}
		processVar(((AOneIvarLst) variables).getIvar(), getOutType(node
				.getTypename()),isHidden(node));
	}

	private boolean isHidden(AOneDecl node) {
		return node.getVisible() instanceof AHiddenVisible;
	}

	public void outABitTypename(ABitTypename node) {
		setOut(node, new BitType());
	}

	public void outAByteTypename(AByteTypename node) {
		setOut(node, byteType());
	}

	public void outAShortTypename(AShortTypename node) {
		setOut(node, new ShortType());
	}

	public void outAIntTypename(AIntTypename node) {
		setOut(node, new IntType());
	}

	public void outABoolTypename(ABoolTypename node) {
		setOut(node, boolType());
	}

	public void outAPidTypename(APidTypename node) {
		setOut(node, new PidType());
	}

	public void outAMtypeTypename(AMtypeTypename node) {
		setOut(node, new MtypeType());
	}

	public void outAChanTypename(AChanTypename node) {
		setOut(node, new ChanType(factory.freshTypeVariable()));
	}

	public void outAUnameTypename(AUnameTypename node) {
		String name = node.getName().getText();
		if (!(env.get(name) instanceof TypeEntry)) {
			addError(node.getName(), new ElementDoesNotExistError(name,USER_TYPE));
		} else {
			setOut(node, new RecordType(name));
		}
	}

	public void caseAInit(AInit node) {
		env.put(ProctypeEntry.initProctypeName,ProctypeEntry.initProctypeEntry);
		currentProctype = ProctypeEntry.initProctypeEntry;
		env.openScope();
		node.getSequence().apply(this);
		currentProctype.setLocalVariableTypeInfo(env.getTopEntries());
		env.closeScope();
	}
	
	public void outAAssignmentAssignment(AAssignmentAssignment node) {
		Type leftType = getOutType(node.getVarref());
		Type rightType = getOutType(node.getExpr());

		if ((leftType != null) && (rightType != null)) {

			if (isChan(leftType) || isChan(rightType)) {
				postEqualityConstraint(leftType, rightType,
						node.getAssign());
			} else if (!(rightType.isSubtype(leftType))) {
				addError(node.getAssign(), new AssignmentMismatchError(leftType
						.name(), rightType.name()));
			}
		}
	}

	public void outAIncrementAssignment(AIncrementAssignment node) {
		if(Type.checkingSymmetry() && getOut(node) instanceof PidType) {
			errorTable.add(node.getPlusPlus().getLine(),new ArithmeticOnPidError());
		}
		
		checkForNotNumericError(getOutType(node.getVarref()), node
				.getPlusPlus(), Error.UNARY);
	}

	public void outADecrementAssignment(ADecrementAssignment node) {
		if(Type.checkingSymmetry() && getOut(node) instanceof PidType) {
			errorTable.add(node.getMinusMinus().getLine(),new ArithmeticOnPidError());
		}
		
		checkForNotNumericError(getOutType(node.getVarref()), node
				.getMinusMinus(), Error.UNARY);
	}

	public void outARecordVarref(ARecordVarref node) {

		Type t = getOutType(node.getVarref());
		if (t != null) {
			if (!(t instanceof RecordType)) {
				addError(node.getDot(), new VariableNotRecordError(t.name()));
			} else {
				Type fieldType = ((TypeEntry)env.get(t.name())).getFieldType(node.getName()
						.getText());
				if (fieldType == null) {
					addError(node.getDot(), new ElementDoesNotExistError(node
							.getName().getText(), FIELD, t.name()));
				} else if (node.getArrayref() == null) {
					setOut(node, fieldType);
				} else if (fieldType instanceof ArrayType) {
					setOut(node, ((ArrayType) fieldType).getElementType());
					if (getArrayIndexType(node) != null) {
						postEqualityConstraint(((ArrayType) fieldType)
								.getIndexType(), getArrayIndexType(node), node
								.getName());
					}
				} else {
					addError(node.getDot(), new VariableNotArrayError(node.getName().getText(),fieldType
							.name()));
				}
			}
		}
	}

	public void outASingleVarref(ASingleVarref node) {
		EnvEntry entry = env.get(node.getName().getText());
		if ((entry instanceof MtypeEntry) && (node.getArrayref() == null)) {
			setOut(node, new MtypeType());
		} else if (!(entry instanceof VarEntry)) {
			addError(node.getName(), new ElementDoesNotExistError(node
					.getName().getText(),VARIABLE));
		} else {
			Type t = ((VarEntry) entry).getType();
			
			if (isArray(t) && hasArrayReference(node)) {
				
				setOut(node, ((ArrayType) t).getElementType());
				if (getArrayIndexType(node) != null) {
					postSubtypingConstraint(getArrayIndexType(node), ((ArrayType) t)
							.getIndexType(), node
							.getName());
					if(Type.checkingSymmetry() && getArrayIndexType(node) instanceof PidType && ((ArrayType)t).getLength()!=(Type.noProcesses()+1) && ((ArrayType)t).getLength()!=0) {
						// The length of a pid-indexed array should be n+1, where n is the number of running processes.
						// This is so that it can be indexed by the process identifiers 1, 2, ... , n.  Unfortunately, index
						// 0 is usually wasted (unless the init process uses it).
						// We don't add an error if the length is zero.  An error has either already
						// been reported about this, or the length has been set to zero by default as
						// there was an error with the initialiser.
						addError(node.getName(), new PidIndexedArrayWithWrongLengthError(node.getName().getText(),((ArrayType)t).getLength(),Type.noProcesses()));
						((ArrayType)t).zeroLength(); // Do this so that the error will not be reported again
					}
				}
			} else if (!isArray(t) && hasArrayReference(node)) {
				addError(node.getName(), new VariableNotArrayError(node.getName().getText(),t.name()));
			} else {
				setOut(node, t);
			}
		}
	}

	private boolean hasArrayReference(ASingleVarref node) {
		return node.getArrayref() != null;
	}

	private Type getArrayIndexType(ASingleVarref node) {
		return getOutType(((AArrayref) node.getArrayref()).getExpr());
	}

	private Type getArrayIndexType(ARecordVarref node) {
		return getOutType(((AArrayref) node.getArrayref()).getExpr());
	}
	
	public void outAArrayref(AArrayref node) {
		Type exprType = getOutType(node.getExpr());
		if ((exprType != null) && !isByteOrPidSubtype(exprType)) {
			addError(node.getLBracket(), new SubtypingError(exprType.name(),byteType().name()));
		}
	}

	private boolean isByteOrPidSubtype(Type exprType) {
		return exprType.isSubtype(new ByteType()) || exprType.isSubtype(new PidType());
	}

	public void outARunFactor(ARunFactor node) {

		EnvEntry entry = env.get(node.getName().getText());
		if (!(entry instanceof ProctypeEntry)) {
			addError(node.getName(), new ElementDoesNotExistError(node.getName()
					.getText(),PROCTYPE));
		} else {
			if (node.getArgLst() == null) {
				typeCheckRunArguments(proctypeFormalArgs(entry), new ArrayList(),
						node.getName());
			} else {
				typeCheckRunArguments(proctypeFormalArgs(entry),
						(List) getOut(node.getArgLst()), node.getName());
			}
		}
	}

	private List proctypeFormalArgs(EnvEntry entry) {
		return ((ProctypeEntry) entry).getArgTypes();
	}

	private void typeCheckRunArguments(List formalArgTypes, List actualArgTypes,
			TName proctypeName) {

		checkCorrectNumberOfActualArgs(formalArgTypes, actualArgTypes, proctypeName);

		for (int i = 0; i < minSize(formalArgTypes, actualArgTypes); i++) {
			if ((actualArgTypes.get(i) != null)
					&& (formalArgTypes.get(i) != null)) {
				postSubtypingConstraint((Type) actualArgTypes
						.get(i), (Type) formalArgTypes.get(i), proctypeName);
			}
		}
	}

	private void checkCorrectNumberOfActualArgs(List formalArgs, List actualArgs, TName proctypeName) {
		if (formalArgs.size() != actualArgs.size()) {
			addError(proctypeName, new WrongNumArgsError(
					proctypeName.getText(), formalArgs.size(),
					actualArgs.size()));
		}
	}

	private int minSize(List x, List y) {
		return Math.min(x.size(), y.size());
	}

	public void outAConditionalExpr(AConditionalExpr node) {
		Type condType = getOutType(node.getIf());
		Type thenType = getOutType(node.getThen());
		Type elseType = getOutType(node.getElse());

		if ((condType != null) && (!isBoolSubtype(condType))) {
			addError(node.getRightarrow(), new IfCondError(condType.name()));
		}

		if ((thenType != null) && (elseType != null)) {

			if (isChan(thenType) && isChan(elseType)) {
				postEqualityConstraint(thenType, elseType,
						node.getRightarrow());
				setOut(node, thenType);
			} else {
				try {
					setOut(node, Type.max(thenType, elseType));
				} catch (IncomparableTypesException e) {
					addError(node.getRightarrow(), new IfMismatchError(thenType
							.name(), elseType.name()));
				}
			}
		}
	}

	public void outACompoundOrExpr(ACompoundOrExpr node) {
		Type leftType = getOutType(node.getAndExpr());
		Type rightType = getOutType(node.getOrExpr());

		checkForNotBoolError(leftType, rightType, node.getOr());

		setOut(node, boolType());
	}

	private boolean isBoolSubtype(Type t) {
		return t.isSubtype(new BoolType());
	}

	public void outACompoundAndExpr(ACompoundAndExpr node) {
		
		Type leftType = getOutType(node.getBitorExpr());
		Type rightType = getOutType(node.getAndExpr());

		checkForNotBoolError(leftType, rightType, node.getAnd());

		setOut(node, boolType());
	}

	public void outACompoundBitorExpr(ACompoundBitorExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitor(),
				getOutType(node.getBitxorExpr()), getOutType(node
						.getBitorExpr()));
	}

	public void outACompoundBitxorExpr(ACompoundBitxorExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitxor(),
				getOutType(node.getBitandExpr()), getOutType(node
						.getBitxorExpr()));
	}

	public void outACompoundBitandExpr(ACompoundBitandExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitand(),
				getOutType(node.getEqExpr()), getOutType(node.getBitandExpr()));
	}

	public void outACompoundEqExpr(ACompoundEqExpr node) {
		Type leftType = getOutType(node.getRelExpr());
		Type rightType = getOutType(node.getEqExpr());

		if ((leftType != null) && (rightType != null)) {
			if (isChan(leftType) && isChan(rightType)) {
				setOut(node, boolType());
			} else if (!((leftType.isSubtype(rightType)) || (rightType
					.isSubtype(leftType)))) {
				addError(node.getEqop(), new EqMismatchError(leftType.name(),
						rightType.name(), node.getEqop().getText()));
			} else
				setOut(node, boolType());
		}
	}

	public void outASimpleEqExpr(ASimpleEqExpr node) {
		setOut(node, getOut(node.getRelExpr()));
	}

	public void outACompoundrelopRelExpr(ACompoundrelopRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getRelop(),
				getOutType(node.getShiftExpr()), getOutType(node.getRelExpr()));
	}

	public void outACompoundgtRelExpr(ACompoundgtRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getGt(), getOutType(node
				.getShiftExpr()), getOutType(node.getRelExpr()));
	}

	public void outACompoundltRelExpr(ACompoundltRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getLt(), getOutType(node
				.getShiftExpr()), getOutType(node.getRelExpr()));
	}

	public void outACompoundShiftExpr(ACompoundShiftExpr node) {
		if (checkBothSidesNumeric(getOutType(node.getAddExpr()),
				getOutType(node.getShiftExpr()), node.getShiftop())) {
			Type outType = getOutType(node.getAddExpr());
			outType.setNotPidLiteral();
			setOut(node, outType);
		}
	}

	public void outACompoundplusAddExpr(ACompoundplusAddExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getPlus(),
				getOutType(node.getMultExpr()), getOutType(node.getAddExpr()));
	}

	public void outACompoundminusAddExpr(ACompoundminusAddExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getMinus(),
				getOutType(node.getMultExpr()), getOutType(node.getAddExpr()));
	}

	public void outACompoundMultExpr(ACompoundMultExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getMultop(),
				getOutType(node.getUnExpr()), getOutType(node.getMultExpr()));
	}

	public void outANotUnExpr(ANotUnExpr node) {
		Type t = getOutType(node.getFactor());
		if (t != null) {
			if (t.isSubtype(boolType())) {
				t.setNotPidLiteral();
				setOut(node, t);
			} else {
				addError(node.getBang(), new NotBoolError(t.name(), node
						.getBang().getText(), Error.UNARY));
			}
		}
	}

	public void outAComplementUnExpr(AComplementUnExpr node) {
		Type t = getOutType(node.getFactor());
		if (t != null) {
			if (isNumeric(t)) {
				setOut(node, t);
			} else {
				addError(node.getComplement(), new NotNumericError(t.name(),
						node.getComplement().getText(), Error.UNARY));
			}
		}
	}

	public void outASimpleExpr(ASimpleExpr node) {
		setOut(node, getOut(node.getOrExpr()));
	}

	public void outASimpleOrExpr(ASimpleOrExpr node) {
		setOut(node, getOut(node.getAndExpr()));
	}

	public void outASimpleAndExpr(ASimpleAndExpr node) {
		setOut(node, getOut(node.getBitorExpr()));
	}

	public void outASimpleBitorExpr(ASimpleBitorExpr node) {
		setOut(node, getOut(node.getBitxorExpr()));
	}

	public void outASimpleBitxorExpr(ASimpleBitxorExpr node) {
		setOut(node, getOut(node.getBitandExpr()));
	}

	public void outASimpleBitandExpr(ASimpleBitandExpr node) {
		setOut(node, getOut(node.getEqExpr()));
	}

	public void outASimpleRelExpr(ASimpleRelExpr node) {
		setOut(node, getOut(node.getShiftExpr()));
	}

	public void outASimpleAddExpr(ASimpleAddExpr node) {
		setOut(node, getOut(node.getMultExpr()));
	}

	public void outASimpleShiftExpr(ASimpleShiftExpr node) {
		setOut(node, getOut(node.getAddExpr()));
	}

	public void outASimpleMultExpr(ASimpleMultExpr node) {
		setOut(node, getOut(node.getUnExpr()));
	}

	public void outASimpleUnExpr(ASimpleUnExpr node) {
		setOut(node, getOut(node.getFactor()));
	}

	public void outAParentheseFactor(AParentheseFactor node) {
		setOut(node, getOut(node.getExpr()));
	}

	public void outAConstFactor(AConstFactor node) {
		setOut(node, getOut(node.getConst()));
	}

	public void outATrueConst(ATrueConst node) {
		setOut(node, boolType());
	}

	public void outAPidConst(APidConst node) {
		setOut(node, new PidType());
	}

	public void outAUnderscoreConst(AUnderscoreConst node) {
		setOut(node, factory.freshTypeVariable());
	}
	
	public void outAFalseConst(AFalseConst node) {
		setOut(node, boolType());
	}

	public void outATimeoutFactor(ATimeoutFactor node) {
		setOut(node, boolType());
	}

	public void outANonprogressFactor(ANonprogressFactor node) {
		setOut(node, boolType());
	}

	public void outAVarrefFactor(AVarrefFactor node) {
		setOut(node, getOut(node.getVarref()));
	}

	public void outAChanopFactor(AChanopFactor node) {
		Type varType = getOutType(node.getVarref());
		if (varType != null) {

			if (!isChan(varType)) {
				addError(node.getLParenthese(), new VariableNotChannelError(
						varType.name()));
			}

			else {
				setOut(node, boolType());
			}
		}
	}

	public void outALengthFactor(ALengthFactor node) {
		Type varType = getOutType(node.getVarref());
		if (varType != null) {
			if (!isChan(varType)) {
				addError(node.getLParenthese(), new VariableNotChannelError(
						varType.name()));
			}

			else {
				setOut(node, byteType());
			}
		}
	}

	public void outANumberConst(ANumberConst node) {
		long val = Long.parseLong(node.getNumber().getText());

		if (valueOutOfLegalRange(val)) {
			addError(node.getNumber(), new LiteralValueTooLargeError(val));
		} else if (node.getMinus() == null) {
			setOut(node, NumericType.typeOfNumericLiteral(val));
		} else {
			setOut(node, NumericType.typeOfNumericLiteral(val * (-1)));
		}
	}

	private boolean valueOutOfLegalRange(long val) {
		return val > NumericType.MAX_INT || val < NumericType.MIN_INT;
	}

	public void outAAssertStmnt(AAssertStmnt node) {
		Type type = getOutType(node.getExpr());
		if ((type != null) && !type.isSubtype(boolType())) {
			addError(node.getAssert(), new SubtypingError(type.name(),boolType().name()));
		}
	}
	
	public void outAElseStmnt(AElseStmnt node) {
		// Unimplemented - Check that :: precedes this else
	}

	public void outABreakStmnt(ABreakStmnt node) {
		// Unimplemented - Check that the break statement is within a do..od
		// loop
	}

	private void processSend(PVarref chan, PSendArgs args, Token bang) {
		processCommunication(chan, (List) getOut(args), bang);
	}

	private void processReceive(PVarref chan, PRecvArgs args, Token query) {
		processCommunication(chan, (List) getOut(args), query);
	}
	
	public void processCommunication(PVarref chan, List argTypes, Token operator) {
		if ((getOutType(chan) != null) && (argTypes!=null)) {
			List<Type> typeVariables = createTypeVariablesForCommunication(operator,
					argTypes);
			postEqualityConstraint(
					new ChanType(typeVariables), (getOutType(chan)), operator);
		}
	}

	public void outAListSendArgs(AListSendArgs node) {
		setOut(node, getOut(node.getArgLst()));
	}

	@SuppressWarnings("unchecked")
	public void outAHeadedListSendArgs(AHeadedlistSendArgs node) {
		List<Type> tailTypes = (List<Type>)getOut(node.getArgLst());
		if ((tailTypes) != null && (getOut(node.getExpr()) != null)) {
			tailTypes.add(0, (Type)getOut(node.getExpr()));
			setOut(node, tailTypes);
		}
	}

	public void outAOneArgLst(AOneArgLst node) {
		setOut(node, processArg(node.getExpr()));
	}

	public void outAOneRecvArgs(AOneRecvArgs node) {
		setOut(node, processArg(node.getRecvArg()));
	}

	public void outAManyArgLst(AManyArgLst node) {
		setOut(node, processArgs(node.getExpr(), node.getArgLst()));
	}

	@SuppressWarnings("unchecked")
	private List<Type> processArgs(Node head, Node tail) {
		List<Type> argumentTypes = (List<Type>) getOut(tail);
		argumentTypes.add(0, (Type)getOut(head));
		return argumentTypes;
	}

	private List<Type> processArg(Node arg) {
		List<Type> argumentType = new ArrayList<Type>();
		argumentType.add((Type)getOut(arg));
		return argumentType;
	}

	public void outAOneTypenamelst(AOneTypenamelst node) {
		setOut(node, processArg(node.getTypename()));
	}

	public void outAManyTypenamelst(AManyTypenamelst node) {
		setOut(node, processArgs(node.getTypename(), node.getTypenamelst()));
	}

	private List<Type> createTypeVariablesForCommunication(Token operator,
			List actualArgTypes) {
		List<Type> typeVariables = new ArrayList<Type>();
		for (int i = 0; i < actualArgTypes.size(); i++) {
			addTypeVariableForArgType(typeVariables, (Type) actualArgTypes
					.get(i), operator);
		}
		return typeVariables;
	}

	private void addTypeVariableForArgType(List<Type> variables, Type argType,
			Token operator) {

		TypeVariableType tv = factory.freshTypeVariable();
		if (isBang(operator) || isTypeOfNumericConstant(argType)) {
			postSubtypingConstraint(argType, tv, operator);
		} else {
			postSubtypingConstraint(tv, argType, operator);
		}
		variables.add(tv);
	}

	private boolean isTypeOfNumericConstant(Type t) {
		return isNumeric(t) && ((NumericType) t).isTypeOfConstant();
	}

	private boolean isBang(Token operator) {
		return operator instanceof TBang || operator instanceof TBangBang;
	}

	public void outAFifoSend(AFifoSend node) {
		processSend(node.getVarref(), node.getSendArgs(), node.getBang());
	}

	public void outASortedSend(ASortedSend node) {
		processSend(node.getVarref(), node.getSendArgs(), node.getBangBang());
	}

	public void outAFifoReceive(AFifoReceive node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node.getQuery());
	}

	public void outARandomReceive(ARandomReceive node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node
				.getQueryQuery());
	}

	public void outAFifopollReceive(AFifopollReceive node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node.getQuery());
		setOut(node,new BoolType());
	}

	public void outARandompollReceive(ARandompollReceive node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node
				.getQueryQuery());
		setOut(node,new BoolType());
	}

	public void outAFifoRecvPoll(AFifoRecvPoll node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node.getQuery());
		setOut(node, boolType());
	}

	public void outARandomRecvPoll(ARandomRecvPoll node) {
		processReceive(node.getVarref(), node.getRecvArgs(), node
				.getQueryQuery());
		setOut(node, boolType());
	}

	public void outAManyheadedRecvArgs(AManyheadedRecvArgs node) {
		setOut(node, processArgs(node.getRecvArg(), node.getRecvArgs()));
	}

	public void outAManyRecvArgs(AManyRecvArgs node) {
		setOut(node, processArgs(node.getRecvArg(), node.getRecvArgs()));
	}

	public void outAVarRecvArg(AVarRecvArg node) {
		setOut(node, getOut(node.getVarref()));
	}

	public void outAEvalRecvArg(AEvalRecvArg node) {
		Type t = getOutType(node.getExpr());
		if (isNumeric(t)) {
			((NumericType) t).setIsTypeOfConstant();
		}
		setOut(node, t);
	}

	public void outAConstRecvArg(AConstRecvArg node) {
		setOut(node, getOut(node.getConst()));
	}

	public void caseAProctype(AProctype node) {
		dealWithEnabler(node);
		env.openScope();
		dealWithDeclarations(node);

		currentProctype = getParameterNamesAndTypes(node.getDeclLst());

		EnvEntry existingEntry = env.putGlobal(node.getName().getText(),currentProctype);
		if (existingEntry != null) {
			addError(node.getName(), new NameAlreadyUsedError(node.getName().getText(),existingEntry));
		}
		node.getSequence().apply(this);
		
		//((ProctypeEntry)env.get(node.getName().getText())).setLocalVariableTypeInfo(env.getTopVariables());
		currentProctype.setLocalVariableTypeInfo(env.getTopEntries());
		
		env.closeScope();
	}

	private ProctypeEntry getParameterNamesAndTypes(PDeclLst parameters) {
		List<Type> argTypes = new ArrayList<Type>();
		List<String> argNames = new ArrayList<String>();
		if (parameters != null) {
			while (parameters instanceof AManyDeclLst) {
				argTypes.addAll(getArgumentTypes(getNames((AManyDeclLst) parameters)));
				argNames.addAll(getArgumentNames(getNames((AManyDeclLst) parameters)));
				parameters = ((AManyDeclLst) parameters).getDeclLst();
			}
			argTypes.addAll(getArgumentTypes(getNames((AOneDeclLst) parameters)));
			argNames.addAll(getArgumentNames(getNames((AOneDeclLst)parameters)));
		}
		Assert.assertEquals(argTypes.size(),argNames.size());
		
		return new ProctypeEntry(argTypes,argNames);
	}

	private PIvarLst getNames(AOneDeclLst typedArgs) {
		return ((AOneDecl) typedArgs.getOneDecl()).getIvarLst();
	}

	private PIvarLst getNames(AManyDeclLst typedArgs) {
		return ((AOneDecl) typedArgs.getOneDecl()).getIvarLst();
	}

	private void dealWithDeclarations(AProctype node) {
		if (node.getDeclLst() != null) {
			node.getDeclLst().apply(this);
		}
	}

	private void dealWithEnabler(AProctype node) {
		if (node.getEnabler() != null) {
			node.getEnabler().apply(this);
		}
	}

	private boolean checkForNotNumericError(Type t, Token operator, int nature) {
		if (t != null) {
			if (!isNumeric(t)) {
				addError(operator, new NotNumericError(t.name(), operator
						.getText(), nature));
				return false;
			}
			return true;
		}
		return false;
	}

	private boolean checkBothSidesNumeric(Type left, Type right, Token operator) {
		return checkForNotNumericError(left, operator, Error.LEFT)
				&& checkForNotNumericError(right, operator, Error.RIGHT);
	}

	private void checkNumericOperationOnNumericTypes(Node node,
			Token operation, Type leftType, Type rightType) {
		if (checkBothSidesNumeric(leftType, rightType, operation)) {
			if (isNumeric(leftType) && isNumeric(rightType)) {
				try {
					Type max = Type.max(leftType, rightType);
					max.setNotPidLiteral();
					setOut(node, max);
				} catch (IncomparableTypesException e) {
					e.printStackTrace();
					System.exit(1);
				}
			}
		}
	}

	private void checkBooleanOperationOnNumericTypes(Node node,
			Token operation, Type leftType, Type rightType) {
		if (checkBothSidesNumeric(leftType, rightType, operation)) {
			setOut(node, boolType());
		}
	}

	private void checkForNotBoolError(Type t, Token operator, int nature) {
		if (t != null) {
			if (!isBoolSubtype(t)) {
				addError(operator, new NotBoolError(t.name(), operator
						.getText(), nature));
			}
		}
	}

	private void checkForNotBoolError(Type left, Type right, Token operator) {
		checkForNotBoolError(left, operator, Error.LEFT);
		checkForNotBoolError(right, operator, Error.RIGHT);
	}

	private List<String> getArgumentNames(PIvarLst names) {
		List<String> result = new ArrayList<String>();
		while (names instanceof AManyIvarLst) {
			result.add(((ASingleIvar) ((AManyIvarLst) names).getIvar())
					.getName().getText());
			names = ((AManyIvarLst) names).getIvarLst();
		}
		result.add(((ASingleIvar) ((AOneIvarLst) names).getIvar()).getName().getText());
		return result;		
	}
	
	private List<Type> getArgumentTypes(PIvarLst names) {
		List<Type> result = new ArrayList<Type>();
		String currentName;
		while (names instanceof AManyIvarLst) {
			// NEED TO HAVE A TYPE ERROR IF AN ARGUMENT HAS ARRAY.
			// AT THE MOMENT I ASSUME IT DOESN'T AND CAST IT INTO
			// IVARSINGLE
			// ALSO NEED ERROR IF ARGUMENT HAS ASSIGNMENT
			currentName = ((ASingleIvar) ((AManyIvarLst) names).getIvar())
					.getName().getText();
			result.add(((VarEntry) env.get(currentName)).getType());
			names = ((AManyIvarLst) names).getIvarLst();
		}
		currentName = ((ASingleIvar) ((AOneIvarLst) names).getIvar()).getName()
				.getText();
		result.add(((VarEntry) env.get(currentName)).getType());
		return result;
	}

	private void processVar(PIvar var, Type groupType, boolean isHidden) {
		Type individualType = groupType;
		
		if (isChan(groupType)) {
			individualType = new ChanType(factory.freshTypeVariable());
		}

		if (var instanceof AArrayIvar) {
			int length;

			Type initType = (Type) getOut(((AArrayIvar) var).getConst());
			if (initType != null) {
				if(!initType.isSubtype(byteType())) {
					addError(((AArrayIvar) var).getName(),new SubtypingError(initType.name(),byteType().name()));
					length = 0; // Set the length to be an undefined value, and carry on type-checking.
				} else {
					length = Integer.parseInt(((ANumberConst)((AArrayIvar)var).getConst()).getNumber().getText());
					if(length==0) {
						addError(((AArrayIvar) var).getName(),new ArrayWithLengthZeroError());
					}
				}
			} else {
				return;
			}

			individualType = new ArrayType(groupType,factory.freshTypeVariable(),length);

			checkVar(((AArrayIvar) var).getIvarassignment(), ((AArrayIvar) var)
					.getName(), individualType, isHidden);
		}

		if (var instanceof ASingleIvar) {
			checkVar(((ASingleIvar) var).getIvarassignment(),
					((ASingleIvar) var).getName(), individualType, isHidden);
		}
	}

	private void checkVar(PIvarassignment assignment, TName name,
			Type type, boolean isHidden) {
		if (assignment instanceof AVariableIvarassignment) {
			checkVariableInitialisation((AVariableIvarassignment)assignment, type);
		}

		if (assignment instanceof AChannelIvarassignment) {
			checkChannelInitialisation((AChannelIvarassignment)assignment, type);
			addStaticChannelToEnvironment(name,type,(AChannelIvarassignment) assignment, isHidden);
			return;
		}
		
		addVariableToEnvironment(name, type, isHidden);
	}

	private void addVariableToEnvironment(TName name, Type type, boolean isHidden) {
		if ((!inTypedef && nameExists(name.getText())) || nameExistsInTopScope(name.getText())) {
			addError(name, new NameAlreadyUsedError(name.getText(),env.get(name.getText())));
		} else {
			if(inTypedef) {
				typedefFieldNames.add(name.getText());
				typedefFieldTypes.add(type);
			}
			env.put(name.getText(), new VarEntry(type,isHidden));
		}
	}
	
	private void addStaticChannelToEnvironment(TName name, Type type, AChannelIvarassignment assignment, boolean isHidden) {
		if ((!inTypedef && nameExists(name.getText())) || nameExistsInTopScope(name.getText())) {
			addError(name, new NameAlreadyUsedError(name.getText(),env.get(name.getText())));
		} else {
			int length = Integer.parseInt(((ANumberConst) assignment.getConst())
					.getNumber().getText());

			if(inTypedef) {
				typedefFieldNames.add(name.getText());
				typedefFieldTypes.add(type);
			}
			env.put(name.getText(),new ChannelEntry(new VarEntry(type,isHidden),length));
		}
	}

	private void checkVariableInitialisation(AVariableIvarassignment assignment, Type type) {
		Type assignType = getOutType(assignment.getExpr());
		if (assignType != null) {
			if (isChan(assignType)) {
				postEqualityConstraint(type, assignType,assignment.getAssign());
			} else if (isArray(type)) {
				if(!assignType.isSubtype(((ArrayType)type).getElementType())) {
				addError(assignment.getAssign(), new AssignmentMismatchError(
						((ArrayType)type).getElementType().name(), assignType.name()));
				}
			} else if (!(assignType.isSubtype(type))) {
				addError(assignment.getAssign(), new AssignmentMismatchError(
						type.name(), assignType.name()));
			}
		}
	}

	private void checkChannelInitialisation(AChannelIvarassignment assignment, Type type) {
		if (getChannelAssignmentTypeList(assignment) != null) {
			if (isChan(type)) {
				postEqualityConstraint(type, getChannelAssignmentType(assignment), assignment.getAssign());
			} else if(isArray(type) && isChan(((ArrayType)type).getElementType())) {
				postEqualityConstraint(((ArrayType)type).getElementType(), getChannelAssignmentType(assignment), assignment.getAssign());
			} else {
				addError(assignment.getAssign(),new AssignmentMismatchError(
						type.name(),getChannelAssignmentType(assignment).name()));
			}
		}
	}

	private ChanType getChannelAssignmentType(AChannelIvarassignment assignment) {
		return new ChanType(getChannelAssignmentTypeList(assignment));
	}

	@SuppressWarnings("unchecked")
	private List<Type> getChannelAssignmentTypeList(AChannelIvarassignment assignment) {
		return (List<Type>) getOut(assignment.getTypenamelst());
	}
	
	private boolean nameExistsInTopScope(String name) {
		return env.getLocal(name) != null;
	}

	private void exitTypedef() {
		env.closeScope();
		inTypedef = false;
	}

	private void enterTypedef() {
		env.openScope();
		inTypedef = true;
		typedefFieldNames = new ArrayList<String>();
		typedefFieldTypes = new ArrayList<Type>();
	}

	protected void addError(Token t, Error e) {
		
		if(callStack.isEmpty()) {
			errorTable.add(t.getLine(), e);
		} else {
			errorTable.add(t.getLine(),callStack,e);
		}
	}

	private void postEqualityConstraint(Type left, Type right, Token tok) {
		constraintSet.add(new EqualityConstraint(left,right,tok.getLine()));
	}

	private void postSubtypingConstraint(Type left, Type right, Token tok) {
		constraintSet.add(new SubtypingConstraint(left,right,tok.getLine()));
	}

	private Type getOutType(Node n) {
		return (Type) getOut(n);
	}

	private BoolType boolType() {
		return new BoolType();
	}

	private ByteType byteType() {
		return new ByteType();
	}

	private boolean isChan(Type t) {
		return t instanceof ChanType;
	}

	private boolean isNumeric(Type t) {
		return t instanceof NumericType || (!Type.checkingSymmetry() && (t instanceof PidType));
	}

	private boolean isArray(Type t) {
		return (t instanceof ArrayType);
	}


}
