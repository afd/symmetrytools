package src.etch.checker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.Environment;
import src.etch.env.InlineEntry;
import src.etch.env.MtypeEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.TypeEntry;
import src.etch.env.VarEntry;
import src.etch.error.ArrayWithLengthZeroError;
import src.etch.error.AssertAppliedToNonBooleanError;
import src.etch.error.AssignmentMismatchError;
import src.etch.error.BadArrayIndexError;
import src.etch.error.CommunicationOnNonChannelError;
import src.etch.error.ElementDoesNotExistError;
import src.etch.error.EqMismatchError;
import src.etch.error.Error;
import src.etch.error.ErrorTable;
import src.etch.error.IfCondError;
import src.etch.error.IfMismatchError;
import src.etch.error.IncomparableTypesException;
import src.etch.error.InlineMacroDoesNotExistError;
import src.etch.error.JumpToUndefinedLabelError;
import src.etch.error.LiteralValueTooLargeError;
import src.etch.error.NameAlreadyUsedError;
import src.etch.error.NotBoolError;
import src.etch.error.NotNumericError;
import src.etch.error.RecordUsedAsExpressionStatement;
import src.etch.error.SemiColonInParenthesesError;
import src.etch.error.SubtypingError;
import src.etch.error.VariableNotArrayError;
import src.etch.error.VariableNotChannelError;
import src.etch.error.VariableNotRecordError;
import src.etch.error.WrongNumParameters;
import src.etch.typeinference.ConstraintSet;
import src.etch.typeinference.EqualityConstraint;
import src.etch.typeinference.Substituter;
import src.etch.typeinference.SubtypingConstraint;
import src.etch.typeinference.Unifier;
import src.etch.types.AnyType;
import src.etch.types.ArrayType;
import src.etch.types.BitType;
import src.etch.types.BoolType;
import src.etch.types.BottomType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.EtchTypeFactory;
import src.etch.types.IntType;
import src.etch.types.Minimiser;
import src.etch.types.MtypeType;
import src.etch.types.NumericType;
import src.etch.types.RecordType;
import src.etch.types.ShortType;
import src.etch.types.Type;
import src.etch.types.TypeFactory;
import src.etch.types.TypeVariableFactory;
import src.etch.types.TypeVariableType;
import src.etch.types.VisibleType;
import src.promela.NodeHelper;
import src.promela.node.*;
import src.utilities.CommandLineSwitch;
import src.utilities.Config;
import src.utilities.StringHelper;

public class Checker extends InlineProcessor {
	
	protected ErrorTable errorTable = new ErrorTable();

	protected ConstraintSet constraintSet;

	private TypeVariableFactory factory = new TypeVariableFactory('X',false);

	protected boolean inTypedef = false;

	private List<Integer> callStackLineNumbers = new ArrayList<Integer>();
	private List<String> callStackNames = new ArrayList<String>();
	
	private static final String USER_TYPE = "user defined type";
	private static final String PROCTYPE = "proctype";
	private static final String VARIABLE = "variable";
	private static final String FIELD = "field";
	
	protected ProctypeEntry currentProctype = null;

	private List<String> typedefFieldNames = new ArrayList<String>();

	private List<VisibleType> typedefFieldTypes = new ArrayList<VisibleType>();

	private Map<String,List<Integer>> gotoDestinations;

	public static TypeFactory theFactory = null;
	
	/* This token is used for generating line numbers for error messages when it is hard
	 * to get a line number from an AST node (e.g. for an expression)
	 */
	private Token lastIdentifierToken = null;

	public Checker() {
		Checker.theFactory = new EtchTypeFactory();
		constraintSet = new ConstraintSet(new Unifier());
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
	
	public Environment getEnv() {
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
			env.put(name, new MtypeEntry(tok.getLine()));
		}
	}
	
	public void caseAUtype(AUtype node) {
		enterTypedef();

		node.getDeclLst().apply(this);
		String name = node.getName().getText();

		EnvEntry alreadyExists = env.putGlobal(name, new TypeEntry(typedefFieldNames, typedefFieldTypes, node.getName().getLine()));
		if(alreadyExists != null) {
			addError(node.getName(), new NameAlreadyUsedError(name,alreadyExists));
		}

		exitTypedef();
	}

	public void outAOneDecl(AOneDecl node) {
		PIvarLst variables = node.getIvarLst();
		VisibleType type = getOutVisibleType(node.getTypename());
		while (variables instanceof AManyIvarLst) {
			processVar(((AManyIvarLst) variables).getIvar(), type,isHidden(node));
			variables = ((AManyIvarLst) variables).getIvarLst();
		}
		processVar(((AOneIvarLst) variables).getIvar(), type,isHidden(node));
	}

	private boolean isHidden(AOneDecl node) {
		return node.getVisible() instanceof AHiddenVisible;
	}

	public void outABitTypename(ABitTypename node) {
		setOut(node, bitType());
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
		setOut(node, Checker.theFactory.generateByteType());
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
		VisibleType leftType = getOutVisibleType(node.getVarref());
		VisibleType rightType = getOutVisibleType(node.getOrExpr());

		if ( null == leftType || null == rightType ) {
			return;
		}
		
		if (isNumeric(leftType) && isNumeric(rightType) && !Config.commandLineSwitchIsSet(CommandLineSwitch.STRICTASSIGNMENT)) {
			return;
		}

		if (isChan(leftType) && isChan(rightType)) {
			/* Can we optimise this so that we only post equality constraints between the field types of leftType and rightType? */
			postEqualityConstraint(leftType, rightType,
					node.getAssign());
		} else if (!(rightType.isSubtype(leftType))) {
			addError(node.getAssign(), new AssignmentMismatchError(leftType, rightType));
		}
	}

	public void outAIncrementAssignment(AIncrementAssignment node) {
		checkForNotNumericError(getOutVisibleType(node.getVarref()), node
				.getPlusPlus(), Error.UNARY, getNameFromVarref(node.getVarref()));
	}

	public void outADecrementAssignment(ADecrementAssignment node) {
		checkForNotNumericError(getOutVisibleType(node.getVarref()), node
				.getMinusMinus(), Error.UNARY, getNameFromVarref(node.getVarref()));
	}

	private String getNameFromVarref(PVarref node) {
		String result = "";
		
		PVarref temp = node;
		
		while(temp instanceof ARecordVarref) {
			String encloser = ((ARecordVarref)temp).getName().getText();
			if(((ARecordVarref)temp).getArrayref()!=null) {
				encloser += "[]";
			}
			
			result = (result.equals("") ? encloser : encloser + "." + result);

			temp = ((ARecordVarref)temp).getVarref();
		}

		String encloser = ((ASingleVarref)temp).getName().getText();
		if(((ASingleVarref)temp).getArrayref()!=null) {
			encloser += "[]";
		}

		result = (result.equals("") ? encloser : encloser + "." + result);
		
		return result;
	}
	
	
	public void outASingleVarref(ASingleVarref node) {

		EnvEntry entry = env.get(NodeHelper.getNameFromVaribableReference(node).getText());
		if ((entry instanceof MtypeEntry) && (node.getArrayref() == null)) {
			setOut(node, new MtypeType());
			return;
		}
		
		if (!(entry instanceof VarEntry)) {
			addError(NodeHelper.getNameFromVaribableReference(node), new ElementDoesNotExistError(NodeHelper.getNameFromVaribableReference(node).getText(),VARIABLE));
			return;
		}

		checkVariableReferenceIsWellFormed(node, ((VarEntry) entry).getType());
	}

	public void outARecordVarref(ARecordVarref node) {

		VisibleType t = getOutVisibleType(node.getVarref());

		if(t==null) {
			return;
		}
		
		if (!(t instanceof RecordType)) {
			addError(node.getDot(), new VariableNotRecordError(StringHelper.removeWhitespace(node.toString()), t));
			return;
		} 
		
		VisibleType fieldType = ((TypeEntry)env.get(t.name())).getFieldType(node.getName()
						.getText());
		if (fieldType == null) {
			addError(node.getDot(), new ElementDoesNotExistError(node
					.getName().getText(), FIELD, t.name()));
			return;
		}

		checkVariableReferenceIsWellFormed(node,fieldType);
	}

	private void checkVariableReferenceIsWellFormed(PVarref node, VisibleType t) {
		
		if (!NodeHelper.hasArrayReference(node)) {
			setOut(node, t);
			return;
		} else if(t instanceof ArrayType) {
			VisibleType elementType = ((ArrayType) t).getElementType();
			
			setOut(node, elementType);
			dealWithArrayIndex(node,t);
		} else {
			addError(NodeHelper.getNameFromVaribableReference(node), new VariableNotArrayError(NodeHelper.getNameFromVaribableReference(node).getText(), t));
		}
	}

	protected void dealWithArrayIndex(PVarref node, VisibleType t) {
		// This method is overriddent to provide more specialised behaviour
	}
	
	public void inALabel(ALabel node) {
		String name = node.getName().getText();
		if(nameExists(name)) {
			/* Maybe this is conservative -- it will give an error if you try to declare
			 * a label with the same name as a variable.  Not sure whether SPIN would allow
			 * this.
			 */
			addError(node.getName(), new NameAlreadyUsedError(name,env.get(name)));
		} else {
			env.put(name, new LabelEntry(node.getName().getLine()));
		}
	}

	public void outAGotoSimpleStmnt(AGotoSimpleStmnt node) {
		String name = node.getName().getText();
		List<Integer> destinations;
		if(gotoDestinations.containsKey(name)) {
			destinations = gotoDestinations.get(name);
			destinations.add(node.getName().getLine());
		} else {
			destinations = new ArrayList<Integer>();
			destinations.add(node.getName().getLine());
		}
		gotoDestinations.put(name,destinations);
	}
	
	
	private NumericType maxArrayIndexType() {
		return !Config.commandLineSwitchIsSet(CommandLineSwitch.STRICTARRAYINDEXING) ? intType() : byteType();
	}
	
	public void outAArrayref(AArrayref node) {
		Type exprType = getOutType(node.getOrExpr());
		if ((exprType != null) && !suitableTypeForArrayIndex(exprType)) {
			addError(node.getLBracket(), new BadArrayIndexError(exprType, maxArrayIndexType()));
		}
	}

	protected boolean suitableTypeForArrayIndex(Type exprType) {
		return exprType.isSubtype(maxArrayIndexType());
	}

	@SuppressWarnings("unchecked")
	public void outARunFactor(ARunFactor node) {

		EnvEntry entry = env.get(node.getName().getText());
		if (!(entry instanceof ProctypeEntry)) {
			addError(node.getName(), new ElementDoesNotExistError(node.getName()
					.getText(),PROCTYPE));
		} else {
			if (node.getArgLst() == null) {
				typeCheckRunArguments(proctypeFormalArgs(entry), new ArrayList<VisibleType>(),
						node.getName(),(ProctypeEntry) entry);
			} else {
				typeCheckRunArguments(proctypeFormalArgs(entry),
						(List<VisibleType>) getOut(node.getArgLst()), node.getName(),(ProctypeEntry) entry);
			}
		}
	}

	private List<VisibleType> proctypeFormalArgs(EnvEntry entry) {
		return ((ProctypeEntry) entry).getArgTypes();
	}

	private void typeCheckRunArguments(List<VisibleType> formalArgTypes, List<VisibleType> actualArgTypes,
			TName proctypeName, ProctypeEntry entry) {

		checkCorrectNumberOfActualArgs(formalArgTypes, actualArgTypes, proctypeName);

		for (int i = 0; i < Math.min(formalArgTypes.size(), actualArgTypes.size()); i++) {
			if ((actualArgTypes.get(i) != null)
					&& (formalArgTypes.get(i) != null)) {
				
				/* In practice, we don't need type inference here so we could
				 * replace this with a subtyping check and get better error messages.
				 * We would need to post an equality constraint if both formalArgTypes(i)
				 * and actualArgTypes(i) were channels.
				 */

				postSubtypingConstraint(actualArgTypes.get(i),
						formalArgTypes.get(i), proctypeName);

			}
		}
	}

	private void checkCorrectNumberOfActualArgs(List<VisibleType> formalArgs, List<VisibleType> actualArgs, TName proctypeName) {
		if (formalArgs.size() != actualArgs.size()) {
			addError(proctypeName, new WrongNumParameters(
					proctypeName.getText(), formalArgs.size(),
					actualArgs.size()));
		}
	}

	public void outAConditionalFactor(AConditionalFactor node) {
		VisibleType condType = getOutVisibleType(node.getIf());
		VisibleType thenType = getOutVisibleType(node.getThen());
		VisibleType elseType = getOutVisibleType(node.getElse());
		
		if(node.getSeparator().getText().equals(";")) {
			addError(node.getSeparator(), new SemiColonInParenthesesError());
		}
		
		if ((condType != null) && (!isBoolSubtype(condType))) {
			addError(node.getSeparator(), new IfCondError(condType));
		}

		if ((thenType != null) && (elseType != null)) {

			if (isChan(thenType) && isChan(elseType)) {
				postEqualityConstraint(thenType, elseType,
						node.getSeparator());
				setOut(node, thenType);
			} else {
				try {
					setOut(node, AnyType.max(thenType, elseType));
				} catch(IncomparableTypesException e) {
					addError(node.getSeparator(), new IfMismatchError(thenType, elseType));
				}
			}
		}
	}

	public void outACompoundOrExpr(ACompoundOrExpr node) {
		VisibleType leftType = getOutVisibleType(node.getAndExpr());
		VisibleType rightType = getOutVisibleType(node.getOrExpr());

		checkForNotBoolError(leftType, rightType, node.getOr());

		setOut(node, boolType());
	}

	private boolean isBoolSubtype(Type t) {
		return t.isSubtype(new BoolType());
	}

	public void outACompoundAndExpr(ACompoundAndExpr node) {
		
		VisibleType leftType = getOutVisibleType(node.getBitorExpr());
		VisibleType rightType = getOutVisibleType(node.getAndExpr());

		checkForNotBoolError(leftType, rightType, node.getAnd());

		setOut(node, boolType());
	}

	public void outACompoundBitorExpr(ACompoundBitorExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitor(),
				getOutVisibleType(node.getBitxorExpr()), getOutVisibleType(node
						.getBitorExpr()));
	}

	public void outACompoundBitxorExpr(ACompoundBitxorExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitxor(),
				getOutVisibleType(node.getBitandExpr()), getOutVisibleType(node
						.getBitxorExpr()));
	}

	public void outACompoundBitandExpr(ACompoundBitandExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getBitand(),
				getOutVisibleType(node.getEqExpr()), getOutVisibleType(node.getBitandExpr()));
	}

	public void outACompoundEqExpr(ACompoundEqExpr node) {
		VisibleType leftType = getOutVisibleType(node.getRelExpr());
		VisibleType rightType = getOutVisibleType(node.getEqExpr());

		if ((leftType != null) && (rightType != null)) {
			if (isChan(leftType) && isChan(rightType)) {
				postEqualityConstraint(leftType,rightType,node.getEqop());
				setOut(node, boolType());
			} else if (!((leftType.isSubtype(rightType)) || (rightType
					.isSubtype(leftType)))) {
				addError(node.getEqop(), new EqMismatchError(leftType,
						rightType, node));
			} else
				setOut(node, boolType());
		}
	}

	public void outASimpleEqExpr(ASimpleEqExpr node) {
		setOut(node, getOut(node.getRelExpr()));
	}

	public void outACompoundrelopRelExpr(ACompoundrelopRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getRelop(),
				getOutVisibleType(node.getShiftExpr()), getOutVisibleType(node.getRelExpr()));
	}

	public void outACompoundgtRelExpr(ACompoundgtRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getGt(), getOutVisibleType(node
				.getShiftExpr()), getOutVisibleType(node.getRelExpr()));
	}

	public void outACompoundltRelExpr(ACompoundltRelExpr node) {
		checkBooleanOperationOnNumericTypes(node, node.getLt(), getOutVisibleType(node
				.getShiftExpr()), getOutVisibleType(node.getRelExpr()));
	}

	public void outACompoundShiftExpr(ACompoundShiftExpr node) {
		if (checkBothSidesNumeric(getOutVisibleType(node.getAddExpr()),
				getOutVisibleType(node.getShiftExpr()), node.getShiftop())) {
			VisibleType outType = getOutVisibleType(node.getAddExpr());
			setOut(node, outType);
		}
	}

	public void outACompoundplusAddExpr(ACompoundplusAddExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getPlus(),
				getOutVisibleType(node.getMultExpr()), getOutVisibleType(node.getAddExpr()));
	}

	public void outACompoundminusAddExpr(ACompoundminusAddExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getMinus(),
				getOutVisibleType(node.getMultExpr()), getOutVisibleType(node.getAddExpr()));
	}

	public void outACompoundMultExpr(ACompoundMultExpr node) {
		checkNumericOperationOnNumericTypes(node, node.getMultop(),
				getOutVisibleType(node.getUnExpr()), getOutVisibleType(node.getMultExpr()));
	}

	public void outANotUnExpr(ANotUnExpr node) {
		VisibleType t = getOutVisibleType(node.getFactor());
		if (t != null) {
			if (t.isSubtype(boolType())) {
				setOut(node, t);
			} else {
				addError(node.getBang(), new NotBoolError(t, node
						.getBang().getText(), Error.UNARY));
			}
		}
	}

	public void outAComplementUnExpr(AComplementUnExpr node) {
		VisibleType t = getOutVisibleType(node.getFactor());
		if (t != null) {
			if (isNumeric(t)) {
				setOut(node, t);
			} else {
				addError(node.getComplement(), new NotNumericError(t,
						node.getComplement().getText(), Error.UNARY));
			}
		}
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
		setOut(node, getOut(node.getOrExpr()));
	}

	public void outAConstFactor(AConstFactor node) {
		setOut(node, getOut(node.getConst()));
	}

	public void outATrueConst(ATrueConst node) {
		setOut(node, boolType());
	}

	public void outAPidConst(APidConst node) {
		setOut(node, Checker.theFactory.generateByteType());
	}

	public void outANrPrConst(ANrPrConst node) {
		setOut(node, Checker.theFactory.generateByteType());
	}

	public void outAUnderscoreConst(AUnderscoreConst node) {
		setOut(node, BottomType.uniqueInstance);
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
		VisibleType varType = getOutVisibleType(node.getVarref());
		if (varType != null) {

			if (!isChan(varType)) {
				addError(node.getLParenthese(), new VariableNotChannelError(
						varType, node.getChanop()));
			}

			else {
				setOut(node, boolType());
			}
		}
	}

	public void outALengthFactor(ALengthFactor node) {
		VisibleType varType = getOutVisibleType(node.getVarref());
		if (varType != null) {
			if (!isChan(varType)) {
				addError(node.getLParenthese(), new VariableNotChannelError(
						varType, node.getLen()));
			}

			else {
				setOut(node, byteType());
			}
		}
	}

	public void outANumberConst(ANumberConst node) {

		try {
			long val = Long.parseLong(node.getNumber().getText())*(node.getMinus() == null ? 1 : -1);
			if (valueOutOfLegalRange(val)) {
				addError(node.getNumber(), new LiteralValueTooLargeError(val));
			} else {
				setOut(node, Checker.theFactory.generateTypeForNumericLiteral(val));
			}
		} catch(NumberFormatException e) {
			addError(node.getNumber(), new LiteralValueTooLargeError(node.getNumber().getText()));
		}
	}

	private boolean valueOutOfLegalRange(long val) {
		return val > NumericType.MAX_INT || val < NumericType.MIN_INT;
	}

	public void outAAssertSimpleStmnt(AAssertSimpleStmnt node) {
		VisibleType type = getOutVisibleType(node.getOrExpr());
		if ((type != null) && !type.isSubtype(boolType())) {
			addError(node.getAssert(), new AssertAppliedToNonBooleanError(type));
		}
	}
	
	public void outAElseSimpleStmnt(AElseSimpleStmnt node) {
		// Unimplemented - Check that :: precedes this else
	}

	public void outABreakSimpleStmnt(ABreakSimpleStmnt node) {
		// Unimplemented - Check that the break statement is within a do..od
		// loop
	}

	@SuppressWarnings("unchecked")
	private void processSend(PVarref chan, PSendArgs args, Token bang) {
		processCommunication(chan, (List<VisibleType>) getOut(args), bang);
	}

	@SuppressWarnings("unchecked")
	private void processReceive(PVarref chan, PRecvArgs args, Token query) {
		processCommunication(chan, (List<VisibleType>) getOut(args), query);
	}
	
	public void processCommunication(PVarref chan, List<VisibleType> argTypes, Token operator) {
		Type type = getOutType(chan);
		
		if (type != null) {
			
			if(!(type instanceof ChanType)) {
				
				addError(operator, new CommunicationOnNonChannelError(operator, type));
				
			} else if (argTypes!=null) {
				
				List<Type> typeVariables = createTypeVariablesForCommunication(operator,
						argTypes);
				if(typeVariables!=null) {
					postEqualityConstraint(
						new ChanType(typeVariables), type, operator);
				}
			}
		}
	}

	public void outAListSendArgs(AListSendArgs node) {
		setOut(node, getOut(node.getArgLst()));
	}

	@SuppressWarnings("unchecked")
	public void outAHeadedlistSendArgs(AHeadedlistSendArgs node) {
		List<Type> tailTypes = (List<Type>)getOut(node.getArgLst());
		if ((tailTypes) != null && (getOut(node.getOrExpr()) != null)) {
			tailTypes.add(0, getOutType(node.getOrExpr()));
			setOut(node, tailTypes);
		}
	}

	public void outAOneArgLst(AOneArgLst node) {
		setOut(node, processArg(node.getOrExpr()));
	}

	public void outAOneRecvArgs(AOneRecvArgs node) {
		setOut(node, processArg(node.getRecvArg()));
	}

	public void outAManyArgLst(AManyArgLst node) {
		setOut(node, processArgs(node.getOrExpr(), node.getArgLst()));
	}

	@SuppressWarnings("unchecked")
	private List<Type> processArgs(Node head, Node tail) {
		List<Type> argumentTypes = (List<Type>) getOut(tail);
		argumentTypes.add(0, getOutType(head));
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
			List<VisibleType> actualArgTypes) {
		List<Type> typeVariables = new ArrayList<Type>();
		for (int i = 0; i < actualArgTypes.size(); i++) {
			if(actualArgTypes.get(i)==null) {
				return null;
			}

			addTypeVariableForArgType(typeVariables, actualArgTypes
					.get(i), operator);
		}
		return typeVariables;
	}

	private void addTypeVariableForArgType(List<Type> variables, VisibleType argType,
			Token operator) {

		TypeVariableType tv = factory.freshTypeVariable();
		if(argType != null) {
			if (isBang(operator) || isTypeOfNumericConstant(argType) || argType.equal(BottomType.uniqueInstance)) {
				postSubtypingConstraint(argType, tv, operator);
			} else {
				postSubtypingConstraint(tv, argType, operator);
			}
		}
		variables.add(tv);
	}

	private boolean isTypeOfNumericConstant(VisibleType t) {
		return (t instanceof NumericType) && ((NumericType) t).isTypeOfConstant();
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
		VisibleType t = getOutVisibleType(node.getOrExpr());
		if (isNumeric(t)) {
			((NumericType) t).setIsTypeOfConstant();
		}
		setOut(node, t);
	}

	public void outAConstRecvArg(AConstRecvArg node) {
		setOut(node, getOut(node.getConst()));
	}
	
	public void caseTName(TName node) {
		lastIdentifierToken = node;
	}
	
	public void outAExpressionSimpleStmnt(AExpressionSimpleStmnt node) {
		/* This method checks that records are not used as expression statements */
		if(null != getOut(node.getOrExpr())) {
			Type t = (Type)getOut(node.getOrExpr());
			if(t instanceof RecordType) {
				addError(lastIdentifierToken, new RecordUsedAsExpressionStatement(((RecordType)t).name()));
			}
		}
		
	}

	public void caseAProctype(AProctype node) {
		dealWithEnabler(node);
		env.openScope();

		gotoDestinations = new HashMap<String,List<Integer>>();

		dealWithDeclarations(node);
		
		currentProctype = getParameterNamesAndTypes(node.getParamLst(),node.getName().getLine());

		EnvEntry existingEntry = env.putGlobal(node.getName().getText(),currentProctype);
		if (existingEntry != null) {
			addError(node.getName(), new NameAlreadyUsedError(node.getName().getText(),existingEntry));
		}
		node.getSequence().apply(this);
		
		//((ProctypeEntry)env.get(node.getName().getText())).setLocalVariableTypeInfo(env.getTopVariables());
		currentProctype.setLocalVariableTypeInfo(env.getTopEntries());
		
		resolveGotos();

		env.closeScope();
	}

	private void resolveGotos() {
		for(String labelName : gotoDestinations.keySet()) {
			EnvEntry entry = env.get(labelName);
			if(!(entry instanceof LabelEntry)) {
				for(Integer i : gotoDestinations.get(labelName)) {
					errorTable.add(i,new JumpToUndefinedLabelError(labelName,entry));
				}
			}
		}
	}

	private ProctypeEntry getParameterNamesAndTypes(PParamLst parameters, int lineOfDeclaration) {
		List<VisibleType> argTypes = new ArrayList<VisibleType>();
		List<String> argNames = new ArrayList<String>();
		if (parameters != null) {
			while (parameters instanceof AManyParamLst) {
				argTypes.addAll(getArgumentTypes(getNames((AManyParamLst) parameters)));
				argNames.addAll(getArgumentNames(getNames((AManyParamLst) parameters)));
				parameters = ((AManyParamLst) parameters).getParamLst();
			}
			argTypes.addAll(getArgumentTypes(getNames((AOneParamLst) parameters)));
			argNames.addAll(getArgumentNames(getNames((AOneParamLst)parameters)));
		}
		assert(argTypes.size()==argNames.size());
		
		return new ProctypeEntry(argTypes,argNames,lineOfDeclaration);
	}

	private PIvarLst getNames(AOneParamLst typedArgs) {
		return ((AOneDecl) typedArgs.getOneDecl()).getIvarLst();
	}

	private PIvarLst getNames(AManyParamLst typedArgs) {
		return ((AOneDecl) typedArgs.getOneDecl()).getIvarLst();
	}

	private void dealWithDeclarations(AProctype node) {
		if (node.getParamLst() != null) {
			node.getParamLst().apply(this);
		}
	}

	private void dealWithEnabler(AProctype node) {
		if (node.getEnabler() != null) {
			node.getEnabler().apply(this);
		}
	}

	private boolean checkForNotNumericError(VisibleType t, Token operator, int nature, String variableName) {
		if (t != null) {
			if (!isNumeric(t)) {
				addError(operator, new NotNumericError(t, operator
						.getText(), nature, variableName));
				return false;
			}
			return true;
		}
		return false;
	}

	private boolean checkForNotNumericError(VisibleType t, Token operator, int nature) {
		return checkForNotNumericError(t, operator, nature, null);
	}
	
	private boolean checkBothSidesNumeric(VisibleType left, VisibleType right, Token operator) {
		return checkForNotNumericError(left, operator, Error.LEFT)
				&& checkForNotNumericError(right, operator, Error.RIGHT);
	}

	protected void checkNumericOperationOnNumericTypes(Node node,
			Token operation, VisibleType leftType, VisibleType rightType) {
		if (checkBothSidesNumeric(leftType, rightType, operation)) {
			if (isNumeric(leftType) && isNumeric(rightType)) {
				try {
					Type max = AnyType.max(leftType, rightType);
					setOut(node, max);
				} catch(IncomparableTypesException e) {
					assert(false);
					e.printStackTrace();
				}
			}
		}
	}

	private void checkBooleanOperationOnNumericTypes(Node node,
			Token operation, VisibleType leftType, VisibleType rightType) {
		if (checkBothSidesNumeric(leftType, rightType, operation)) {
			setOut(node, boolType());
		}
	}

	private void checkForNotBoolError(VisibleType t, Token operator, int nature) {
		if (t != null) {
			if (!isBoolSubtype(t)) {
				addError(operator, new NotBoolError(t, operator
						.getText(), nature));
			}
		}
	}

	private void checkForNotBoolError(VisibleType left, VisibleType right, Token operator) {
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
	
	private List<VisibleType> getArgumentTypes(PIvarLst names) {
		List<VisibleType> result = new ArrayList<VisibleType>();
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

	private void processVar(PIvar var, VisibleType groupType, boolean isHidden) {
		VisibleType individualType = groupType;
		
		if (isChan(groupType)) {
			individualType = new ChanType(factory.freshTypeVariable());
		}

		if (var instanceof AArrayIvar) {
			int length;

			VisibleType initType = (VisibleType) getOut(((AArrayIvar) var).getConst());
			if (initType != null) {
				if(!initType.isSubtype(byteType())) {
					addError(((AArrayIvar) var).getName(),new SubtypingError(initType, byteType()));
					length = 0; // Set the length to be an undefined value, and carry on type-checking.
				} else {
					length = Integer.parseInt(((ANumberConst)((AArrayIvar)var).getConst()).getNumber().getText());
					if(length==0) {
						addError(((AArrayIvar) var).getName(),new ArrayWithLengthZeroError(((AArrayIvar) var).getName().getText()));
					}
				}
			} else {
				return;
			}

			individualType = Checker.theFactory.generateArrayType(groupType,factory.freshTypeVariable(),length);

			checkVar(((AArrayIvar) var).getIvarassignment(), ((AArrayIvar) var)
					.getName(), individualType, isHidden);
		}

		if (var instanceof ASingleIvar) {
			checkVar(((ASingleIvar) var).getIvarassignment(),
					((ASingleIvar) var).getName(), individualType, isHidden);
		}
	}

	private void checkVar(PIvarassignment assignment, TName name,
			VisibleType type, boolean isHidden) {
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

	private void addVariableToEnvironment(TName name, VisibleType type, boolean isHidden) {
		
		if ((!inTypedef && nameExists(name.getText())) || nameExistsInTopScope(name.getText())) {
			addError(name, new NameAlreadyUsedError(name.getText(),env.get(name.getText())));
		} else {
			if(inTypedef) {
				typedefFieldNames.add(name.getText());
				typedefFieldTypes.add(type);
			}
			env.put(name.getText(), new VarEntry(type, isHidden, name.getLine()));
		}
	}
	
	private void addStaticChannelToEnvironment(TName name, VisibleType type, AChannelIvarassignment assignment, boolean isHidden) {
		if ((!inTypedef && nameExists(name.getText())) || nameExistsInTopScope(name.getText())) {
			addError(name, new NameAlreadyUsedError(name.getText(),env.get(name.getText())));
		} else {
			int length = Integer.parseInt(((ANumberConst) assignment.getConst())
					.getNumber().getText());

			if(inTypedef) {
				typedefFieldNames.add(name.getText());
				typedefFieldTypes.add(type);
			}
			env.put(name.getText(),new ChannelEntry(new VarEntry(type,isHidden,name.getLine()),length,name.getLine()));
		}
	}

	private void checkVariableInitialisation(AVariableIvarassignment assignment, VisibleType type) {
		VisibleType assignType = getOutVisibleType(assignment.getOrExpr());
		if (assignType != null) {
			if (isChan(type) && isChan(assignType)) {
				postEqualityConstraint(type, assignType,assignment.getAssign());
			} else if (isArray(type)) {
				if(!assignType.isSubtype(((ArrayType)type).getElementType())) {
				addError(assignment.getAssign(), new AssignmentMismatchError(
						((ArrayType)type).getElementType(), assignType));
				}
			} else if (!(assignType.isSubtype(type))) {
				addError(assignment.getAssign(), new AssignmentMismatchError(
						type, assignType));
			}
		}
	}

	private void checkChannelInitialisation(AChannelIvarassignment assignment, VisibleType type) {
		if (getChannelAssignmentTypeList(assignment) != null) {
			if (isChan(type)) {
				if(!Config.commandLineSwitchIsSet(CommandLineSwitch.CHANNELREDUNDANCY)) {
					postEqualityConstraint(type, getChannelAssignmentType(assignment), assignment.getAssign());
				}
			} else if(isArray(type) && isChan(((ArrayType)type).getElementType())) {
				if(!Config.commandLineSwitchIsSet(CommandLineSwitch.CHANNELREDUNDANCY)) {
					postEqualityConstraint(((ArrayType)type).getElementType(), getChannelAssignmentType(assignment), assignment.getAssign());
				}
			} else {
				addError(assignment.getAssign(),new AssignmentMismatchError(
						type, getChannelAssignmentType(assignment)));
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
		typedefFieldTypes = new ArrayList<VisibleType>();
	}

	protected void addError(Token t, Error e) {
				
		if(callStackLineNumbers.isEmpty()) {
			errorTable.add(t.getLine(), e);
		} else {
			errorTable.add(t.getLine(),callStackLineNumbers, callStackNames, e);
		}
	}

	private void postEqualityConstraint(Type left, Type right, Token tok) {

		constraintSet.add(new EqualityConstraint(left,right,tok.getLine()));

	}

	protected void postSubtypingConstraint(Type left, Type right, Token tok) {

		constraintSet.add(new SubtypingConstraint(left,right,tok.getLine()));

	}

	protected Type getOutType(Node n) {
		return (Type) getOut(n);
	}

	private VisibleType getOutVisibleType(Node n) {
		return (VisibleType) getOut(n);
	}

	private BoolType boolType() {
		return new BoolType();
	}
	
	private ByteType byteType() {
		return Checker.theFactory.generateByteType();
	}

	private IntType intType() {
		return new IntType();
	}
	
	private BitType bitType() {
		return Checker.theFactory.generateBitType();
	}
	
	private boolean isChan(VisibleType t) {
		return t instanceof ChanType;
	}

	private boolean isNumeric(VisibleType t) {
		return t instanceof NumericType;
	}

	private boolean isArray(VisibleType t) {
		return (t instanceof ArrayType);
	}

	public void restoreProctypeScope(AProctype node) {
		assert(env.get(node.getName().getText()) instanceof ProctypeEntry);
		env.restoreScope(((ProctypeEntry)getEnvEntry(node.getName().getText())).getLocalScope());
	}
	
	public String showCompleteTypeInformation(String sourceName) {

		String result = "\nReconstructed types for " + sourceName + ":";
		
		for(String entryName : env.getTopEntries().keySet()) {
			EnvEntry entry = env.get(entryName);
			if(entry instanceof ProctypeEntry && !((ProctypeEntry)entry).getLocalScope().isEmpty()) {
				result += "\n  " + entryName + "\n  ";
				for(int i=0; i<entryName.length(); i++) { 
					result += "-"; 
				}
				
				result += "\n";

				
				ProctypeEntry proctypeEntry = (ProctypeEntry)entry;
				Map<String,EnvEntry> scope = proctypeEntry.getLocalScope();
				for(String scopeEntryName : scope.keySet()) {
					EnvEntry scopeEntry = scope.get(scopeEntryName); 
					if(scopeEntry instanceof VarEntry) {
						result += "    " + scopeEntryName + " : " + Minimiser.minimise(((VarEntry)scopeEntry).getType()).name() + "\n";
					}
				}
			}
		}

		result += "\n  Globals\n  -------\n";

		for(String entryName : env.getTopEntries().keySet()) {
			EnvEntry entry = env.get(entryName);
			if(entry instanceof VarEntry) {
				result += "    " + entryName + " : " + Minimiser.minimise(((VarEntry)entry).getType()).name() + "\n";
			}
		}
		
		return result;
		
	}


	@Override
	public void outAInlineSimpleStmnt(AInlineSimpleStmnt node) {
		if(! ( env.get(node.getName().getText()) instanceof InlineEntry )) {
			addError(node.getLParenthese(), new InlineMacroDoesNotExistError(node.getName().getText()));
			return;
		} 
		
		InlineEntry inline = (InlineEntry) env.get(node.getName().getText());

		List<POrExpr> exprList = toListOfExpressions(node.getExprLst());

		if(inline.getArity() != exprList.size()) {
			addError(node.getLParenthese(), new WrongNumParameters(node.getName().getText(), inline.getArity(), 
					exprList.size()));
			return;
		}
		
		if(allExpressionsAreWellTyped(exprList)) {
			
			env.openScope();
			
			callStackLineNumbers.add(node.getLParenthese().getLine());
			callStackNames.add(node.getName().getText());
			
			for(int i =0; i < inline.getArgNames().size(); i++) {
				env.put(inline.getArgNames().get(i), new VarEntry((VisibleType)getOut(exprList.get(i)), false, node.getLParenthese().getLine()));
			}
			
			inline.getCopyOfSequence().apply(this);
			
			callStackLineNumbers.remove(callStackLineNumbers.size()-1);
			callStackNames.remove(callStackNames.size()-1);

			env.closeScope();
			
		}
	
	}

	private boolean allExpressionsAreWellTyped(List<POrExpr> exprList) {
		for(POrExpr expr : exprList) {
			if(!(getOut(expr) instanceof VisibleType)) {
				return false;
			}
		}
		return true;
	}

}
