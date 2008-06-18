package src.symmextractor;

import src.etch.checker.Checker;
import src.etch.env.ProctypeEntry;
import src.etch.types.PidType;
import src.promela.node.AArrayIvar;
import src.promela.node.AChannelIvarassignment;
import src.promela.node.ADecrementAssignment;
import src.promela.node.AIncrementAssignment;
import src.promela.node.AInit;
import src.promela.node.AManyActive;
import src.promela.node.AOneActive;
import src.promela.node.AProctype;
import src.promela.node.ARecordVarref;
import src.promela.node.ARunFactor;
import src.promela.node.ASingleIvar;
import src.promela.node.ASingleVarref;
import src.promela.node.PIvar;
import src.promela.node.PVarref;
import src.promela.node.TActivetok;
import src.symmextractor.error.ActiveProctypeError;
import src.symmextractor.error.DynamicChannelCreationError;
import src.symmextractor.error.DynamicProcessCreationError;
import src.symmextractor.error.GlobalArrayOfChannelsError;
import src.symmextractor.error.UnaryArithmeticOnPidError;

public class SymmetryChecker extends Checker {

	private String currentProctypeName;

	private boolean inProctype = false;
	
	public SymmetryChecker() {
		super(true);
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
			errorTable.add(node.getLBracket().getLine(), new GlobalArrayOfChannelsError( ((AArrayIvar)channel).getName().getText()));
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

	public void outAIncrementAssignment(AIncrementAssignment node) {
		if(getOut(node.getVarref()) instanceof PidType) {
			addError(node.getPlusPlus(), new UnaryArithmeticOnPidError(getNameFromVarref(node.getVarref()), node.getPlusPlus()));
		}
		super.outAIncrementAssignment(node);
	}

	public void outADecrementAssignment(ADecrementAssignment node) {
		if(getOut(node.getVarref()) instanceof PidType) {
			addError(node.getMinusMinus(), new UnaryArithmeticOnPidError(getNameFromVarref(node.getVarref()), node.getMinusMinus()));
		}
		super.outADecrementAssignment(node);
	}

	private String getNameFromVarref(PVarref node) {
		String result = "";
		
		PVarref temp = node;
		
		while(temp instanceof ARecordVarref) {
			String field = ((ARecordVarref)temp).getName().getText();
			if(((ARecordVarref)temp).getArrayref()!=null) {
				field += "[]";
			}
			
			result = (result.equals("") ? field : field + "." + result);

			temp = ((ARecordVarref)temp).getVarref();
		}
		String field = ((ASingleVarref)temp).getName().getText();
		if(((ASingleVarref)temp).getArrayref()!=null) {
			field += "[]";
		}
		
		result = field + "." + result;
		
		return result;
	}
	
	
}

