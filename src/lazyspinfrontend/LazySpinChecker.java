package src.lazyspinfrontend;

import java.util.ArrayList;
import java.util.List;

import src.etch.env.ProcessEntry;
import src.etch.types.ArrayType;
import src.etch.types.VisibleType;
import src.promela.NodeHelper;
import src.promela.node.PVarref;
import src.promela.node.Token;
import src.symmextractor.PidAwareChecker;
import src.symmextractor.error.PidIndexedArrayWithWrongLengthError;
import src.symmextractor.types.PidType;

public class LazySpinChecker extends PidAwareChecker {
	
	public LazySpinChecker(LazySpinFindNumProcesses numProcesses) {
		super();
		setNumberOfRunningProcesses(numProcesses.getNumProcesses());
	}

	
	@Override
	protected void dealWithArrayIndex(PVarref node, VisibleType t) {
		if (getArrayIndexType(node) != null) {
			if(getArrayIndexType(node) instanceof PidType && ((ArrayType)t).getLength()!=(numberOfRunningProcesses()) && ((ArrayType)t).getLength()!=0) {
				addError(NodeHelper.getNameFromVaribableReference(node), new PidIndexedArrayWithWrongLengthError(NodeHelper.getNameFromVaribableReference(node).getText(),((ArrayType)t).getLength(),numberOfRunningProcesses()));
				((ArrayType)t).zeroLength(); // Do this so that the error will not be reported again
			}
			postSubtypingConstraint(getArrayIndexType(node), ((ArrayType) t)
					.getIndexType(), NodeHelper.getNameFromVaribableReference(node));
		}
	}

	protected boolean checkForNotNumericError(VisibleType t, Token operator, int nature, String variableName) {
		if (t instanceof PidType) {
			return true;
		}
		return super.checkForNotNumericError(t, operator, nature, variableName);
	}


	@Override
	public List<String> getProctypeNames() {
		assert(env.getProctypeEntries().size() == 1);
		List<String> result = new ArrayList<String>();
		result.add((String)env.getProctypeEntries().keySet().toArray()[0]);
		return result;
	}


	@Override
	public List<ProcessEntry> getProcessEntries() {
		List<ProcessEntry> result = new ArrayList<ProcessEntry>();
		String proctypeName = (String)env.getProctypeEntries().keySet().toArray()[0];
		for(int i = 0; i < numberOfRunningProcesses(); i++) {
			result.add(new ProcessEntry(proctypeName, new ArrayList<String>()));
		}
		return result;
	}
	
	
}
