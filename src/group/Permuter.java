package src.group;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import src.etch.checker.SymmetrySettings;
import src.etch.env.ProctypeEntry;
import src.etch.env.TypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.VisibleType;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AArrayref;
import src.promela.node.AAssignmentAssignment;
import src.promela.node.ACompoundEqExpr;
import src.promela.node.AConstFactor;
import src.promela.node.AConstRecvArg;
import src.promela.node.AEvalRecvArg;
import src.promela.node.AFifoReceive;
import src.promela.node.AFifoRecvPoll;
import src.promela.node.AFifoSend;
import src.promela.node.AFifopollReceive;
import src.promela.node.AHeadedlistSendArgs;
import src.promela.node.AInit;
import src.promela.node.AListSendArgs;
import src.promela.node.AManyArgLst;
import src.promela.node.AManyRecvArgs;
import src.promela.node.AManySequence;
import src.promela.node.AManyheadedRecvArgs;
import src.promela.node.ANumberConst;
import src.promela.node.AOneArgLst;
import src.promela.node.AOneDecl;
import src.promela.node.AOneRecvArgs;
import src.promela.node.AOneSequence;
import src.promela.node.AProctype;
import src.promela.node.ARandomReceive;
import src.promela.node.ARandomRecvPoll;
import src.promela.node.ARandompollReceive;
import src.promela.node.ARecordVarref;
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
import src.promela.node.ASimpleUnExpr;
import src.promela.node.ASingleVarref;
import src.promela.node.ASortedSend;
import src.promela.node.AVariableIvarassignment;
import src.promela.node.Node;
import src.promela.node.PArgLst;
import src.promela.node.PExpr;
import src.promela.node.PIvar;
import src.promela.node.PRecvArg;
import src.promela.node.PRecvArgs;
import src.promela.node.PSendArgs;
import src.promela.node.PSequence;
import src.promela.node.PStep;
import src.promela.node.PVarref;
import src.promela.node.TName;
import src.promela.node.Token;
import src.symmextractor.StaticChannelDiagramExtractor;

public class Permuter extends DepthFirstAdapter {

	private Permutation alpha;
	private StaticChannelDiagramExtractor typeInfo;
	private VisibleType typename;
	
	public Permuter(Permutation alpha, StaticChannelDiagramExtractor typeInfo) {
		this.typeInfo = typeInfo;
		this.alpha = alpha;
		this.typename = null;
	}

	public void inAProctype(AProctype node) {
		typeInfo.restoreProctypeScope(node);
	}
	
	public void outAProctype(AProctype node) {
		typeInfo.getEnv().closeScope();
	}
	
	protected boolean isArrayIndexedByPid(PVarref varref) {
		PVarref temp = varref;

		Assert.assertTrue(((varref instanceof ASingleVarref && ((ASingleVarref)varref).getArrayref()!=null)
		|| (varref instanceof ARecordVarref && ((ARecordVarref)varref).getArrayref()!=null)));

		List<String> fieldNamesStack = new ArrayList<String>();
		while(temp instanceof ARecordVarref) {
			fieldNamesStack.add(((ARecordVarref)temp).getName().getText());
			temp = ((ARecordVarref)temp).getVarref();
		}

		Assert.assertTrue(typeInfo.getEnvEntry(getVariableName(temp)) instanceof VarEntry);

		VisibleType t = ((VarEntry)typeInfo.getEnvEntry(getVariableName(temp))).getType();
		
		while(!fieldNamesStack.isEmpty()) {
			Assert.assertTrue(t instanceof RecordType || (t instanceof ArrayType && ((ArrayType)t).getElementType() instanceof RecordType));
			String fieldName = (String)fieldNamesStack.remove(fieldNamesStack.size()-1);
			if(t instanceof RecordType) {
				t = ((TypeEntry)typeInfo.getEnvEntry(((RecordType)t).name())).getFieldType(fieldName);
			} else {
				t = ((TypeEntry)typeInfo.getEnvEntry(((RecordType)((ArrayType)t).getElementType()).name())).getFieldType(fieldName);
			}
		}
		
		Assert.assertTrue(t instanceof ArrayType);

		return ((ArrayType)t).getIndexType() instanceof PidType;
	}

	private String getVariableName(PVarref temp) {
		return ((ASingleVarref)temp).getName().getText();
	}

	protected boolean isNumericNode(Node n) {
		try {
			Integer.parseInt(n.toString().substring(0,
					n.toString().length() - 1));
			return true;
		} catch (NumberFormatException e) {
			return false;
		}
	}

	public void inAOneDecl(AOneDecl node) {
		typename = (VisibleType) typeInfo.getOut(node.getTypename());
	}

	public void outAOneDecl(AOneDecl node) {
		typename = null;
	}

	/**
	 * Applies the permutation to a variable name. If the permutation doesn't
	 * act on the name (i.e. the name is not a channel name) then this has no
	 * effect. The method is complicated by the fact that calling toString on a
	 * node results in a space at the end, whereas getText doesn't.
	 * 
	 * @param node
	 *            variable name token.
	 */
	public void caseTName(TName node) {
		// We want to keep variable declaration names fixed.
		if (!(node.parent() instanceof PIvar)) {
			node.setText((String) alpha.apply(node.getText()));
		}
	}

	public void outACompoundEqExpr(ACompoundEqExpr node) {
		VisibleType leftType = (VisibleType) typeInfo.getOut(node.getRelExpr());
		VisibleType rightType = (VisibleType) typeInfo.getOut(node.getEqExpr());

		if (isPid(leftType) && isNumericNode(node.getEqExpr())) {
			permuteToken(((ANumberConst) ((AConstFactor) ((ASimpleUnExpr) ((ASimpleMultExpr) ((ASimpleAddExpr) ((ASimpleShiftExpr) ((ASimpleRelExpr) ((ASimpleEqExpr) node
					.getEqExpr()).getRelExpr()).getShiftExpr()).getAddExpr())
					.getMultExpr()).getUnExpr()).getFactor()).getConst())
					.getNumber());
		}

		else if (isPid(rightType) && isNumericNode(node.getRelExpr())) {
			permuteToken(((ANumberConst) ((AConstFactor) ((ASimpleUnExpr) ((ASimpleMultExpr) ((ASimpleAddExpr) ((ASimpleShiftExpr) ((ASimpleRelExpr) node
					.getRelExpr()).getShiftExpr()).getAddExpr()).getMultExpr())
					.getUnExpr()).getFactor()).getConst()).getNumber());
		}
	}

	public void outAArrayref(AArrayref node) {
		if(isNumericNode(node.getExpr()) && isArrayIndexedByPid((PVarref)node.parent())) {
			permuteNumericExpression(node.getExpr());
		}
	}

	public void outAAssignmentAssignment(AAssignmentAssignment node) {
		VisibleType leftType = (VisibleType) typeInfo.getOut(node.getVarref());

		if (isPid(leftType) && isNumericNode(node.getExpr())) {
			permuteNumericExpression(node.getExpr());
		}
	}

	public void outAVariableIvarassignment(AVariableIvarassignment node) {
		if (isPid(typename)	&& (isNumericNode(node.getExpr())))
			permuteNumericExpression(node.getExpr());
	}

	private void permuteSend(PVarref channel, PSendArgs args) {
		ProductType argTypes = (ProductType) ((ChanType) typeInfo
				.getOut(channel)).getMessageType();

		int i = 0;

		PArgLst arglst;

		if (args instanceof AHeadedlistSendArgs) {
			Assert.assertTrue(argTypes.getTypeOfPosition(i) instanceof VisibleType);
			if (isPid((VisibleType) argTypes.getTypeOfPosition(i))
					&& (isNumericNode(((AHeadedlistSendArgs) args).getExpr()))) {
				permuteNumericExpression(((AHeadedlistSendArgs) args).getExpr());
			}
			arglst = ((AHeadedlistSendArgs) args).getArgLst();
			i++;
		} else {
			arglst = ((AListSendArgs) args).getArgLst();
		}
		
		while (arglst instanceof AManyArgLst) {
			Assert.assertTrue(argTypes.getTypeOfPosition(i) instanceof VisibleType);
			permuteArgument(((AManyArgLst)arglst).getExpr(), (VisibleType) argTypes.getTypeOfPosition(i));
			arglst = ((AManyArgLst) arglst).getArgLst();
			i++;
		}
		Assert.assertTrue(argTypes.getTypeOfPosition(i) instanceof VisibleType);
		permuteArgument(((AOneArgLst)arglst).getExpr(),(VisibleType) argTypes.getTypeOfPosition(i));
	}

	public void outAFifoSend(AFifoSend node) {
		permuteSend(node.getVarref(), node.getSendArgs());
	}

	public void outASortedSend(ASortedSend node) {
		permuteSend(node.getVarref(), node.getSendArgs());
	}

	public void outAFifoReceive(AFifoReceive node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outARandomReceive(ARandomReceive node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outAFifopollReceive(AFifopollReceive node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outARandompollReceive(ARandompollReceive node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outAFifoRecvPoll(AFifoRecvPoll node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outARandomRecvPoll(ARandomRecvPoll node) {
		permuteReceive(node.getVarref(), node.getRecvArgs());
	}

	public void outARunFactor(ARunFactor node) {
		if (node.getArgLst() != null) {
			
			List<VisibleType> argTypes = ((ProctypeEntry)typeInfo.getEnvEntry(node.getName().getText())).getArgTypes();

			PArgLst args;

			int i = 0;
			for(args = node.getArgLst(); args instanceof AManyArgLst; args = ((AManyArgLst) args).getArgLst())
			{
				permuteArgument(((AManyArgLst) args).getExpr(),argTypes.get(i));
				i++;
			}

			permuteArgument(((AOneArgLst) args).getExpr(),argTypes.get(i));
		}
	
		// TODO Sort things out so that RUN statements are permuted
	}

	/* PRIVATE METHODS */

	private void permuteReceive(PVarref channel, PRecvArgs args) {
		
		ProductType argTypes = (ProductType) ((ChanType) typeInfo
				.getOut(channel)).getMessageType();
		
		int i = 0;
		while (!(args instanceof AOneRecvArgs)) {
			Assert.assertTrue(argTypes.getTypeOfPosition(i) instanceof VisibleType);
			if (isPid((VisibleType) argTypes.getTypeOfPosition(i))) {
				PRecvArg arg;
				if (args instanceof AManyRecvArgs) {
					arg = ((AManyRecvArgs) args).getRecvArg();
				}
				else {
					arg = ((AManyheadedRecvArgs) args).getRecvArg();
				}
				if ((arg instanceof AConstRecvArg) && isNumericNode(arg)) {
					permuteToken(((ANumberConst) ((AConstRecvArg) arg).getConst())
							.getNumber());
				}

				else if ((arg instanceof AEvalRecvArg)
						&& isNumericNode(((AEvalRecvArg) arg).getExpr()))
					permuteNumericExpression(((AEvalRecvArg) arg).getExpr());
			}

			if (args instanceof AManyRecvArgs)
				args = ((AManyRecvArgs) args).getRecvArgs();
			else
				args = ((AManyheadedRecvArgs) args).getRecvArgs();
			i++;
		}

		// Now do the last one.
		PRecvArg arg = ((AOneRecvArgs) args).getRecvArg();

		if ((arg instanceof AConstRecvArg) && isNumericNode(arg)) {
			permuteToken(((ANumberConst) ((AConstRecvArg) arg).getConst()).getNumber());
		}

		else if ((arg instanceof AEvalRecvArg)
				&& isNumericNode(((AEvalRecvArg) arg).getExpr()))
			permuteNumericExpression(((AEvalRecvArg) arg).getExpr());
	}
	
	public void outAInit(AInit node) {

		PSequence atomicBlock;
		
		atomicBlock = SymmetrySettings.getStatementsWithinAtomic(node);
		
		List<PStep> runStatements = getRunStatements(atomicBlock);

		applyPermutation(runStatements);

		replaceRunStatements(atomicBlock,runStatements);

	}
	
	private void replaceRunStatements(PSequence atomicBlock, List<PStep> runStatements) {
		PSequence temp = atomicBlock;
		for(int i=0; i<runStatements.size(); i++) {
			if(temp instanceof AManySequence) {
				((AManySequence)temp).setStep(runStatements.get(i));
				temp = ((AManySequence)temp).getSequence();
			} else {
				((AOneSequence)temp).setStep(runStatements.get(i));
			}
		}
	}

	private void applyPermutation(List<PStep> runStatements) {
		List<PStep> temp = new ArrayList<PStep>(runStatements);

		for(int i=0; i<runStatements.size(); i++) {
			// Want runStatement(alpha(i)) to be what runStatement(i) was
			int alpha_i = Integer.parseInt((String)alpha.apply(String.valueOf(i+1)))-1;
			runStatements.set(alpha_i,temp.get(i));
		}		
	}

	private List<PStep> getRunStatements(PSequence atomicBlock) {
		List<PStep> result = new ArrayList<PStep>();
		PSequence temp = atomicBlock;
		for(int i=0; i<typeInfo.getNoProcesses()-1; i++) {
			result.add(temp instanceof AOneSequence ? ((AOneSequence)temp).getStep() : ((AManySequence)temp).getStep());
			if(temp instanceof AManySequence) {
				temp = ((AManySequence)temp).getSequence();
			}
		}
		return result;
	}

	private void permuteArgument(PExpr expr, VisibleType argType) {
		if (isPid(argType) && isNumericNode(expr)) {
			permuteNumericExpression(expr);
		}
	}

	private void permuteNumericExpression(PExpr e) {
		Assert.assertTrue(isNumericNode(e));

		permuteToken(((ANumberConst) ((AConstFactor) ((ASimpleUnExpr) ((ASimpleMultExpr) ((ASimpleAddExpr) ((ASimpleShiftExpr) ((ASimpleRelExpr) ((ASimpleEqExpr) ((ASimpleBitandExpr) ((ASimpleBitxorExpr) ((ASimpleBitorExpr) ((ASimpleAndExpr) ((ASimpleOrExpr) ((ASimpleExpr) e)
				.getOrExpr()).getAndExpr()).getBitorExpr()).getBitxorExpr())
				.getBitandExpr()).getEqExpr()).getRelExpr()).getShiftExpr())
				.getAddExpr()).getMultExpr()).getUnExpr()).getFactor())
				.getConst()).getNumber());

	}

	private void permuteToken(Token t) {
		t.setText((String)alpha.apply(t.getText()));
	}

	private boolean isPid(VisibleType t) {
		return t instanceof PidType;
	}
}
