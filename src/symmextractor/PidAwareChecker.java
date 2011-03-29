package src.symmextractor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import src.etch.checker.Checker;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.ProctypeEntry;
import src.etch.typeinference.ConstraintSet;
import src.etch.types.ByteType;
import src.etch.types.Type;
import src.etch.types.VisibleType;
import src.promela.node.AArrayref;
import src.promela.node.APidConst;
import src.promela.node.APidTypename;
import src.promela.node.ARecordVarref;
import src.promela.node.ASingleVarref;
import src.promela.node.PVarref;
import src.symmextractor.types.PidType;
import src.symmextractor.types.SymmExtractorTypeFactory;
import src.symmreducer.InsensitiveVariableReference;
import src.symmreducer.PidIndexedArrayReference;
import src.symmreducer.SensitiveVariableReference;

public abstract class PidAwareChecker extends Checker {
	
	private static int noProcesses = -1;

	public PidAwareChecker() {
		super(new SymmExtractorTypeFactory(), new ConstraintSet(new PidSensitiveUnifier()));
	}
	
	public abstract List<String> getProctypeNames();

	public abstract List<ProcessEntry> getProcessEntries();

	public ProctypeEntry getProctypeEntryForProcess(int j) {
		return (ProctypeEntry)getEnvEntry(getProcessEntries().get(j).getProctypeName());
	}
	
	public ProctypeEntry getProctypeEntryFromName(String name) {
		return (ProctypeEntry)getEnvEntry(name);
	}

	public int proctypeId(String proctypeName) {
		return getProctypeNames().indexOf(proctypeName);
	}

	public int proctypeId(ProctypeEntry proctype) {
		String proctypeName = null;
		for(String name : env.getTopEntries().keySet())
		{
			if(env.getTopEntries().get(name) == proctype)
			{
				proctypeName = name;
				break;
			}
		}
		assert(null != proctypeName);
		return proctypeId(proctypeName);
	}
	
	public Map<String, EnvEntry> getGlobalVariables() {
		return getEnv().getTopEntries();
	}

	public void outAPidConst(APidConst node) {
		setOut(node, new PidType());
	}

	public void outAPidTypename(APidTypename node) {
		setOut(node, new PidType());
	}

	public static int numberOfRunningProcesses() {
		assert(noProcesses >= 0);
		return noProcesses;
	}
	
	public static void setNumberOfRunningProcesses(int n) {
		noProcesses = n;
	}

	protected Type getArrayIndexType(PVarref node) {
		if(node instanceof ASingleVarref) {
			return getOutType(((AArrayref) ((ASingleVarref)node).getArrayref()).getOrExpr());
		}
		return getOutType(((AArrayref) ((ARecordVarref)node).getArrayref()).getOrExpr());
	}

	protected boolean suitableTypeForArrayIndex(Type exprType) {
		return super.suitableTypeForArrayIndex(exprType) || exprType.isSubtype(new PidType());
	}

	public List<SensitiveVariableReference> sensitiveVariableReferencesForProcess(int j) {

		List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();

		String referencePrefix = "((P" + proctypeId(getProcessEntries().get(j).getProctypeName()) + " *)SEG(s," + j + "))->";
				
		for(Entry<String,VisibleType> entry : getProctypeEntryForProcess(j).variableNameTypePairs()) {
			referencesToPermute.addAll(SensitiveVariableReference.getSensitiveVariableReferences(
					entry.getKey(), entry.getValue(), referencePrefix, this));
		}
		return referencesToPermute;
	}

	public List<PidIndexedArrayReference> sensitivelyIndexedArraysForProcess(int j) {
		List<PidIndexedArrayReference> sensitivelyIndexedArrays = new ArrayList<PidIndexedArrayReference>();

		String referencePrefix = "((P" + proctypeId((getProcessEntries().get(j)).getProctypeName())
		+ " *)SEG(s," + j + "))->";
		
		for (Entry<String,VisibleType> entry : getProctypeEntryForProcess(j).variableNameTypePairs()) {

			sensitivelyIndexedArrays
					.addAll(PidIndexedArrayReference.getSensitivelyIndexedArrayReferences(
							entry.getKey(), entry.getValue(), referencePrefix, this));
		}
		return sensitivelyIndexedArrays;
	}

	public List<InsensitiveVariableReference> insensitiveVariableReferencesForProcess(ProctypeEntry proctype, String processId, String stateName) {

		List<InsensitiveVariableReference> result = new ArrayList<InsensitiveVariableReference>();

		String referencePrefix = "((P" + proctypeId(proctype) + " *)SEG(" + stateName + "," + processId + "))->";
		
		result.add(new InsensitiveVariableReference(referencePrefix + "_p", new ByteType()));
				
		for(Entry<String,VisibleType> entry : proctype.variableNameTypePairs()) {
			result.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences(
					entry.getKey(), entry.getValue(), referencePrefix, this));
		}
		return result;
	}

	
	public List<InsensitiveVariableReference> insensitiveVariableReferencesForProcess(int j, String stateName) {
		return insensitiveVariableReferencesForProcess(getProctypeEntryForProcess(j), String.valueOf(j), stateName);
	}
	
	
	
}
