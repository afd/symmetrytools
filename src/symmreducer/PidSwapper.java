package src.symmreducer;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.List;
import java.util.Map;

import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.VisibleType;
import src.symmextractor.PidAwareChecker;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.types.PidType;
import src.utilities.BooleanOption;
import src.utilities.Config;
import src.utilities.Strategy;

public class PidSwapper {

	private PidAwareChecker typeInfo;
	private OutputStreamWriter permutationFile;
	private SwapVectorizer swapVectorizer;
	private int minIndex;
	
	public PidSwapper(PidAwareChecker typeInfo, OutputStreamWriter permutationFile, int minIndex, SwapVectorizer swapVectorizer) {
		this.typeInfo = typeInfo;
		this.permutationFile = permutationFile;
		this.swapVectorizer = swapVectorizer;
		this.minIndex = minIndex;
	}

	public void writeApplyPrSwapToState(String stateType) throws IOException {
		permutationFile.write("void applyPrSwapToState(" + stateType + " *s, int a, int b) {\n");
		permutationFile.write("   uchar tempPid;\n");
		permutationFile.write("   int slot;\n");

		if(Config.getBooleanOption(BooleanOption.VECTORISE)) {
			swapVectorizer.writeProcessSwaps(permutationFile, "a", "b");
		} else {
			swapGlobalPidVariables(permutationFile,"a","b");
			swapLocalPidVariables(permutationFile, "a", "b");
			if(typeInfo instanceof StaticChannelDiagramExtractor) {
				swapPidReferencesInChannels(permutationFile, "a", "b");
			}
		}
		swapProcesses(permutationFile);
		permutationFile.write("}\n\n");
	}
	
	private void swapGlobalPidVariables(OutputStreamWriter fw, String one, String two) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		String referencePrefix = "s->";

		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {

				if (!(Config.strategy() == Strategy.APPROXMARKERS)) {
					for (SensitiveVariableReference reference : SensitiveVariableReference.getSensitiveVariableReferences(
							name, ((VarEntry) entry).getType(), referencePrefix, typeInfo)) {
						assert(PidType.isPid(reference.getType()));
						fw.write("   if(" + reference
								+ "==" + one + ") {\n");
						fw.write("      " + reference
								+ " = b;\n");
						fw.write("   } else if(" + reference
								+ "==" + two + ") {\n");
						fw.write("      " + reference
								+ " = " + one + ";\n");
						fw.write("   }\n");
					}
				}

				for (PidIndexedArrayReference reference : PidIndexedArrayReference.getSensitivelyIndexedArrayReferences(
						name, ((VarEntry) entry).getType(), referencePrefix, typeInfo)) {
					assert(((ArrayType) reference.getType())
							.getIndexType() instanceof VisibleType);
					assert(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
							.getIndexType()));
					fw.write("   {\n");
					fw.write("       " + ((ArrayType) reference.getType()).getElementType().spinRepresentation() + " temp;\n");
					fw.write("       temp = " + reference
							+ "[" + one + "];\n");
					fw.write("       " + reference + "[" + one + "] = "
							+ reference + "[" + two + "];\n");
					fw.write("       " + reference
							+ "[" + two + "] = temp;\n");
					fw.write("   }\n");
				}
			}
		}
	}

	private void swapLocalPidVariables(OutputStreamWriter fw, String one, String two) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {

			for (SensitiveVariableReference reference : typeInfo.sensitiveVariableReferencesForProcess(j, "s")) {

				assert(PidType.isPid(reference.getType())
						|| ChanType.isChan(reference.getType()));
				if (PidType.isPid(reference.getType())) {
					SymmetryApplier.writeln(fw, SymmetryApplier.applySwapToSensitiveReference(reference.toString(), one, two));
				}
			}

			for (PidIndexedArrayReference reference : typeInfo.sensitivelyIndexedArraysForProcess(j)) {

				assert(((ArrayType) reference.getType())
						.getIndexType() instanceof VisibleType);
				assert(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
						.getIndexType()));
				fw.write("   {\n");
				fw.write("       " + ((ArrayType) reference.getType()).getElementType().spinRepresentation() + " temp;\n");
				fw
						.write("       temp = " + reference
								+ "[" + one + "];\n");
				fw.write("       " + reference + "[" + one + "] = "
						+ reference + "[" + two + "];\n");
				fw
						.write("       " + reference
								+ "[" + two + "] = temp;\n");
				fw.write("   }\n");
			}

			fw.write("\n");
		}

	}

	private void swapPidReferencesInChannels(OutputStreamWriter fw, String one, String two) throws IOException {
		
		if(!(typeInfo instanceof StaticChannelDiagramExtractor)) {
			System.out.println("Error: swapPidReferencesInChannel invoked out of context of symmextractor");
			System.exit(1);
		}

		StaticChannelDiagramExtractor _typeInfo = (StaticChannelDiagramExtractor)typeInfo;
		
		for (int i = 0; i < _typeInfo.getNoStaticChannels(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) _typeInfo
					.getEnvEntry((String) _typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), _typeInfo);

			if (PidType.containsPidType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (PidType.isPid(flattenedFieldTypes.get(j))) {

						SymmetryApplier.writeln(fw, SymmetryApplier.applySwapToSensitiveReference("((Q" + (i + 1) + " *)QSEG(s," + i + "))->contents[slot].fld" + j, one, two));
						
					}
				}
				fw.write("   }\n");
			}
		}

	}

	private void swapProcesses(OutputStreamWriter fw) throws IOException {
		for (int j = minIndex; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			int proctypeIdentifier = typeInfo.proctypeId(proctypeName);
			fw.write("   if(a==" + j + ") {\n");
			swapTwoProcesses(fw, proctypeIdentifier, "a", "b");

			if(Config.getBooleanOption(BooleanOption.VECTORISE)) {
				swapVectorizer.swapTwoProcesses(fw, j, "a", "b");
			}

			fw.write("      return;\n");
			fw.write("   }\n\n");
		}
		
	}

	private void swapTwoProcesses(OutputStreamWriter fw, int proctypeIdentifier, String one, String two) throws IOException {
		fw.write("      P" + proctypeIdentifier + " temp;\n");
		fw.write("      memcpy(&temp,SEG(s," + one + "),sizeof(P"
				+ proctypeIdentifier + "));\n");
		fw.write("      memcpy(SEG(s," + one + "),SEG(s," + two + "),sizeof(P"
				+ proctypeIdentifier + "));\n");
		fw.write("      memcpy(SEG(s," + two + "),&temp,sizeof(P"
				+ proctypeIdentifier + "));\n");
		fw.write("      tempPid = VAR(s," + one + ",_pid,P" + proctypeIdentifier
				+ ");\n");
		fw.write("      VAR(s," + one + ",_pid,P" + proctypeIdentifier
				+ ") = VAR(s," + two + ",_pid,P" + proctypeIdentifier + ");\n");
		fw.write("      VAR(s," + two + ",_pid,P" + proctypeIdentifier
				+ ") = tempPid;\n");
	}
	
}

