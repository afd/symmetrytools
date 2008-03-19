package src.symmreducer;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmreducer.targets.Target;
import src.symmreducer.targets.TargetPC;
import src.symmreducer.targets.TargetPPU;

public class SwapVectorizer {

	private int numberOfPidReferencesToSwap;
	private int numberOfChannelReferencesToSwap;

	private int numberOfGlobalPidVariables;
	private int numberOfPidVariablesForProcess[];
	private int numberOfChannelVariablesForProcess[];
	private int numberOfPidVariablesForChannel[];
	private int numberOfChannelVariablesForChannel[];
	
	private StaticChannelDiagramExtractor typeInfo;

	private Target target;
	
	public SwapVectorizer(StaticChannelDiagramExtractor typeInfo) {
		this.typeInfo = typeInfo;

		numberOfGlobalPidVariables = 0;
		numberOfPidVariablesForProcess = new int[typeInfo.getNoProcesses()];
		numberOfChannelVariablesForProcess = new int[typeInfo.getNoProcesses()];
		numberOfPidVariablesForChannel = new int[typeInfo.getNoStaticChannels()];
		numberOfChannelVariablesForChannel = new int[typeInfo.getNoStaticChannels()];
		
		target = new TargetPC();
	}
	
	public void writeIdSwappingDataStructuresAndProcedures(FileWriter out) throws IOException {



		
		String extractIdentifierVariablesFunctionHeader = "void extractIdentifierVariables(AugmentedState* s) {\n";
		extractIdentifierVariablesFunctionHeader += "   int slot;\n";

		String extractIdentifierVariablesFunctionBody = "";
		String replaceIdentifierVariablesFunction = "void replaceIdentifierVariables(AugmentedState* s) {\n";
		replaceIdentifierVariablesFunction += "   int slot;\n";

		
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		numberOfGlobalPidVariables = 0;
		
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry) && !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List<SensitiveVariableReference> sensitiveVariableReferences = SensitiveVariableReference.getSensitiveVariableReferences(name, ((VarEntry) entry).getType(), "s->state.", typeInfo);
				for(SensitiveVariableReference reference : sensitiveVariableReferences) {
					extractIdentifierVariablesFunctionBody += "   s->process_ids[" + numberOfPidReferencesToSwap + "] = " + reference + ";\n";
					extractIdentifierVariablesFunctionBody += "   " + reference + " = 0;\n\n";
					replaceIdentifierVariablesFunction += reference + " = s->process_ids[" + numberOfPidReferencesToSwap + "];\n\n";
					numberOfPidReferencesToSwap++;
					numberOfGlobalPidVariables++;
				}
			}
		}
		
		for (int i = 0; i < typeInfo.getProcessEntries().size(); i++) {

			numberOfPidVariablesForProcess[i] = 0;

			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries().get(i)).getProctypeName();
			Map<String, EnvEntry> localScope = ((ProctypeEntry) typeInfo.getEnvEntry(proctypeName)).getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {

					String referencePrefix = "((P" + typeInfo.proctypeId(proctypeName) + " *)SEG((&(s->state))," + i + "))->";

					for(SensitiveVariableReference reference : SensitiveVariableReference.getSensitiveVariableReferences(varName, ((VarEntry) localScope.get(varName)).getType(), referencePrefix, typeInfo)) {
						if(PidType.isPid(reference.getType())) {
							extractIdentifierVariablesFunctionBody += "   s->process_ids[" + numberOfPidReferencesToSwap + "] = " + reference + ";\n";
							extractIdentifierVariablesFunctionBody += "   " + reference + " = 0;\n\n";
							replaceIdentifierVariablesFunction += "   " + reference + " = s->process_ids[" + numberOfPidReferencesToSwap + "];\n\n";
							numberOfPidReferencesToSwap++;
							numberOfPidVariablesForProcess[i]++;
						}
					}
				}
			}
		}

		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {

			numberOfPidVariablesForChannel[i] = 0;

			ChannelEntry channelEntry = ((ChannelEntry) typeInfo.getEnvEntry((String) typeInfo.getStaticChannelNames().get(i)));
			ChanType type = (ChanType) channelEntry.getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(), typeInfo);

			if (PidType.containsPidType(flattenedFieldTypes) && channelEntry.getLength()>0) {
				extractIdentifierVariablesFunctionBody += "   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG((&(s->state))," + i
						+ "))->Qlen; slot++) {\n";
				replaceIdentifierVariablesFunction += "   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG((&(s->state))," + i
				+ "))->Qlen; slot++) {\n";

				int numberOfPidTypes = PidType.getNumberOfPidTypes(flattenedFieldTypes);
				
				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (PidType.isPid(flattenedFieldTypes.get(j))) {

						String index = (numberOfPidReferencesToSwap+j) + " + slot*" + numberOfPidTypes;

						extractIdentifierVariablesFunctionBody += "      s->process_ids[" + index + "] = " +
						    "((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + ";\n";
						extractIdentifierVariablesFunctionBody += "      ((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + " = 0;\n";

						replaceIdentifierVariablesFunction += "      ((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + 
						 " = s->process_ids[" + index + "];\n";
						
					}
				}

				extractIdentifierVariablesFunctionBody += "   }\n\n";
				replaceIdentifierVariablesFunction += "   }\n\n";

				numberOfPidReferencesToSwap += numberOfPidTypes*channelEntry.getLength();
				numberOfPidVariablesForChannel[i] += numberOfPidTypes*channelEntry.getLength();
			}
		}

		
		

		for (int i = 0; i < typeInfo.getProcessEntries().size(); i++) {

			numberOfChannelVariablesForProcess[i] = 0;

			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries().get(i)).getProctypeName();
			Map<String, EnvEntry> localScope = ((ProctypeEntry) typeInfo.getEnvEntry(proctypeName)).getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {

					String referencePrefix = "((P" + typeInfo.proctypeId(proctypeName) + " *)SEG((&(s->state))," + i + "))->";

					for(SensitiveVariableReference reference : SensitiveVariableReference.getSensitiveVariableReferences(varName, ((VarEntry) localScope.get(varName)).getType(), referencePrefix, typeInfo)) {
						if(ChanType.isChan(reference.getType())) {
							extractIdentifierVariablesFunctionBody += "   s->channel_ids[" + numberOfChannelReferencesToSwap + "] = " + reference + ";\n";
							extractIdentifierVariablesFunctionBody += "   " + reference + " = 0;\n\n";
							replaceIdentifierVariablesFunction += "   " + reference + " = s->channel_ids[" + numberOfChannelReferencesToSwap + "] = " + reference + ";\n\n";
							numberOfChannelReferencesToSwap++;
							numberOfChannelVariablesForProcess[i]++;
						}
					}
				}
			}
		}
		
		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {
			numberOfChannelVariablesForChannel[i] = 0;

			ChannelEntry channelEntry = ((ChannelEntry) typeInfo.getEnvEntry((String) typeInfo.getStaticChannelNames().get(i)));
			ChanType type = (ChanType) channelEntry.getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(), typeInfo);

			if (ChanType.containsChanType(flattenedFieldTypes) && channelEntry.getLength()>0) {
				extractIdentifierVariablesFunctionBody += "   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG((&(s->state))," + i
						+ "))->Qlen; slot++) {\n";
				replaceIdentifierVariablesFunction += "   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG((&(s->state))," + i
				+ "))->Qlen; slot++) {\n";

				int numberOfChanTypes = ChanType.getNumberOfChanTypes(flattenedFieldTypes);
				
				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (ChanType.isChan(flattenedFieldTypes.get(j))) {

						String index = (numberOfChannelReferencesToSwap+j) + " + slot*" + numberOfChanTypes;

						extractIdentifierVariablesFunctionBody += "      s->channel_ids[" + index + "] = " +
						    "((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + ";\n";
						extractIdentifierVariablesFunctionBody += "      ((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + " = 0;\n";

						replaceIdentifierVariablesFunction += "      ((Q" + (i + 1) + " *)QSEG((&(s->state))," + i + "))->contents[slot].fld" + j + 
						 " = s->channel_ids[" + index + "];\n";
						
					}
				}

				extractIdentifierVariablesFunctionBody += "   }\n\n";
				replaceIdentifierVariablesFunction += "   }\n\n";

				numberOfChannelReferencesToSwap += numberOfChanTypes*channelEntry.getLength();
				numberOfChannelVariablesForChannel[i] += numberOfChanTypes*channelEntry.getLength();
			}
		}

		if(target.requiresAlignment()) {
			numberOfPidReferencesToSwap = roundUp(numberOfPidReferencesToSwap, target.alignmentValue());
			numberOfChannelReferencesToSwap = roundUp(numberOfChannelReferencesToSwap, target.alignmentValue());
		}
		
		extractIdentifierVariablesFunctionBody += "}\n\n";
		replaceIdentifierVariablesFunction += "}\n\n";

		
		
		out.write("\ntypedef struct AugmentedState_s {\n");
		out.write("   State state;\n");
		out.write("   uchar process_ids[" + numberOfPidReferencesToSwap + "]" + alignmentSpecifier() + ";\n");
		out.write("   uchar channel_ids[" + numberOfChannelReferencesToSwap + "]"  + alignmentSpecifier() + ";\n");
		out.write("} AugmentedState;\n\n");

		out.write(target.getVectorUnsignedCharDefinition());
		
		writeAugmentedMemcpy(out);

		writeAugmentedMemcmp(out);

		extractIdentifierVariablesFunctionHeader += "   for(slot=0; slot<" + numberOfPidReferencesToSwap + "; slot++) {\n";
		extractIdentifierVariablesFunctionHeader += "      s->process_ids[slot] = 0;\n";
		extractIdentifierVariablesFunctionHeader += "   }\n\n";
		extractIdentifierVariablesFunctionHeader += "   for(slot=0; slot<" + numberOfChannelReferencesToSwap + "; slot++) {\n";
		extractIdentifierVariablesFunctionHeader += "      s->channel_ids[slot] = 0;\n";
		extractIdentifierVariablesFunctionHeader += "   }\n\n";
		
		out.write(extractIdentifierVariablesFunctionHeader);
		out.write(extractIdentifierVariablesFunctionBody);
		out.write(replaceIdentifierVariablesFunction);

		writeFirstProcessIdentifierForProcessArray(out);
		writeFirstChannelIdentifierForProcessArray(out);
		
		writeFirstProcessIdentifierForChannelArray(out);
		writeFirstChannelIdentifierForChannelArray(out);

		out.write("\n");
	}

	private String alignmentSpecifier() {
		if(target.requiresAlignment()) {
			return " __attribute__((aligned(" + target.alignmentValue() + ")))";
		}
		return "";
	}

	private int roundUp(int x, int multiple) {
		while((x % multiple) != 0) {
			x++;
		}
		return x;
	}

	private void writeFirstProcessIdentifierForProcessArray(FileWriter out) throws IOException {
		out.write("const int first_process_id_for_process[" + typeInfo.getNoProcesses() + "] = { ");
		for(int i=0; i<typeInfo.getNoProcesses(); i++) {
			out.write(String.valueOf(firstProcessIdForProcess(i)));
			if(i<typeInfo.getNoProcesses()-1) {
				out.write(", ");
			}
		}
		out.write("};\n");
	}

	private void writeFirstProcessIdentifierForChannelArray(FileWriter out) throws IOException {
		out.write("const int first_process_id_for_channel[" + typeInfo.getNoStaticChannels() + "] = { ");
		for(int i=0; i<typeInfo.getNoStaticChannels(); i++) {
			out.write(String.valueOf(firstProcessIdForChannel(i)));
			if(i<typeInfo.getNoStaticChannels()-1) {
				out.write(", ");
			}
		}
		out.write("};\n");
	}

	private void writeFirstChannelIdentifierForProcessArray(FileWriter out) throws IOException {
		out.write("const int first_channel_id_for_process[" + typeInfo.getNoProcesses() + "] = { ");
		for(int i=0; i<typeInfo.getNoProcesses(); i++) {
			out.write(String.valueOf(firstChannelIdForProcess(i)));
			if(i<typeInfo.getNoProcesses()-1) {
				out.write(", ");
			}
		}
		out.write("};\n");
	}

	private void writeFirstChannelIdentifierForChannelArray(FileWriter out) throws IOException {
		out.write("const int first_channel_id_for_channel[" + typeInfo.getNoStaticChannels() + "] = { ");
		for(int i=0; i<typeInfo.getNoStaticChannels(); i++) {
			out.write(String.valueOf(firstChannelIdForChannel(i)));
			if(i<typeInfo.getNoStaticChannels()-1) {
				out.write(", ");
			}
		}
		out.write("};\n");
	}
	
	
	private void writeAugmentedMemcmp(FileWriter out) throws IOException {
		out.write("int augmented_memcmp(AugmentedState* s1, AugmentedState* s2, int vsize) {\n");
		out.write("   int temp = memcmp(&(s1->state), &(s2->state), vsize);\n");
		out.write("   return (temp!=0 ? temp : memcmp(&(s1->process_ids[0]), &(s2->process_ids[0]), " + (numberOfPidReferencesToSwap+numberOfChannelReferencesToSwap) + "*sizeof(uchar)));\n");
		out.write("}\n\n");
	}

	private void writeAugmentedMemcpy(FileWriter out) throws IOException {
		out.write("void augmented_memcpy(AugmentedState* dest, AugmentedState* source, int vsize) {\n");
		out.write("   memcpy(&(dest->state), &(source->state), vsize);\n");
		out.write("   memcpy(&(dest->process_ids[0]), &(source->process_ids[0]), " + (numberOfPidReferencesToSwap+numberOfChannelReferencesToSwap) + "*sizeof(uchar));\n");
		out.write("}\n\n");
	}

	public void writeProcessSwaps(FileWriter out, String one, String two) throws IOException {
/*		out.write("\n");
		out.write(target.vectorCharType() + " vec_x;\n");
		out.write(target.vectorCharType() + " vec_a;\n");
		out.write(target.vectorCharType() + " vec_b;\n");
		out.write(target.vectorCharType() + " vec_is_a;\n");
		out.write(target.vectorCharType() + " vec_is_b;\n");

		out.write("\n");
		
		out.write(target.getSplatsInstruction("vec_a", one));
		out.write(target.getSplatsInstruction("vec_b", one));

		for(int i=0; i<numberOfPidReferencesToSwap; i+=16) {
			out.write("vec_x = *(" + target.vectorCharType() + "*)(&(s->process_ids[" + i + "]));\n");

			out.write(target.getCompareEqualInstruction("vec_is_a", "vec_x", "vec_a"));
			out.write(target.getCompareEqualInstruction("vec_is_b", "vec_x", "vec_b"));

			out.write(target.getSelectInstruction("vec_x", "vec_is_a", "vec_b", "vec_x"));
			out.write(target.getSelectInstruction("vec_x", "vec_is_b", "vec_a", "vec_x"));

			out.write("*(" + target.vectorCharType() + "*)(&(s->process_ids[" + i + "])) = vec_x;\n");
			out.write("\n");
		}*/

		for(int i=0; i<numberOfPidReferencesToSwap; i+=16) {

			out.write("   {\n");
			out.write("      " + target.getVectorUnsignedCharTypename() + " x;\n");
		    out.write("      " + target.getVectorUnsignedCharTypename() + " vec_a;\n");
		    out.write("      " + target.getVectorUnsignedCharTypename() + " vec_b;\n");
			out.write("      " + target.getVectorUnsignedCharTypename() + " is_a;\n");
			out.write("      " + target.getVectorUnsignedCharTypename() + " is_b;\n");
	
			out.write("      x = *(" + target.getVectorUnsignedCharTypename() + "*)(&(s->process_ids[" + i + "]));\n");
	
		    out.write(target.getSplatsInstruction("vec_a", "a"));
	
		    out.write(target.getSplatsInstruction("vec_b", "b"));
		    
			out.write(target.getCompareEqualInstruction("is_a", "x", "vec_a"));
	
			out.write(target.getCompareEqualInstruction("is_b", "x", "vec_b"));
	
			out.write(target.getSelectInstruction("x", "is_a", "vec_b", "x"));
			
			out.write(target.getSelectInstruction("x", "is_b", "vec_a", "x"));
	
			out.write("      *(" + target.getVectorUnsignedCharTypename() + "*)(&(s->process_ids[" + i + "])) = x;\n");
		
			out.write("   }\n");
		}			

		
/*		out.write("   for(slot = 0; slot < " + numberOfPidReferencesToSwap + "; slot++) {\n");
		out.write("      if(s->process_ids[slot]==" + one + ") {\n");
		out.write("         s->process_ids[slot] = " + two + ";\n");
		out.write("      }\n");
		out.write("      else if(s->process_ids[slot]==" + two + ") {\n");
		out.write("         s->process_ids[slot] = " + one + ";\n");
		out.write("      }\n");
		out.write("   }\n");*/
	}

	public void writeChannelSwaps(FileWriter out) throws IOException {
		out.write("   for(slot = 0; slot < " + numberOfChannelReferencesToSwap + "; slot++) {\n");
		out.write("      if(s->channel_ids[slot]==a) {\n");
		out.write("         s->channel_ids[slot] = b;\n");
		out.write("      }\n");
		out.write("      else if(s->channel_ids[slot]==b) {\n");
		out.write("         s->channel_ids[slot] = a;\n");
		out.write("      }\n");
		out.write("   }\n");
	}

	
	public void swapTwoProcesses(FileWriter out, int oneProcessId, String one, String two) throws IOException {
		out.write("      {\n");
		if(numberOfPidVariablesForProcess[oneProcessId] > 0) {
			swapIdComponents(out, one, two, numberOfPidVariablesForProcess[oneProcessId], "pid_temps", "process_ids", "first_process_id_for_process");
		}
		if(numberOfChannelVariablesForProcess[oneProcessId] > 0) {
			swapIdComponents(out, one, two, numberOfChannelVariablesForProcess[oneProcessId], "channel_temps", "channel_ids", "first_channel_id_for_process");
		}
		out.write("      }\n");
	}

	
	public void swapTwoChannels(FileWriter out, int oneChannelId, String one, String two) throws IOException {
		out.write("      {\n");
		if(numberOfPidVariablesForChannel[oneChannelId] > 0) {
			swapIdComponents(out, one, two, numberOfPidVariablesForChannel[oneChannelId], "pid_temps", "process_ids", "first_process_id_for_channel");
		}
		if(numberOfChannelVariablesForChannel[oneChannelId] > 0) {
			swapIdComponents(out, one, two, numberOfChannelVariablesForChannel[oneChannelId], "channel_temps", "channel_ids", "first_channel_id_for_channel");
		}
		out.write("      }\n");
	}

	private void swapIdComponents(FileWriter out, String one, String two, int numberOfIdVariables, String tempName, String id_array, String first_id_array) throws IOException {
		out.write("         uchar " + tempName + "[" + numberOfIdVariables + "];\n");
		out.write("         memcpy((char*)" + tempName + ", (char*)(&(s->" + id_array + "[" + first_id_array + "[" + one + "]])), " + numberOfIdVariables + "*sizeof(uchar));\n");
		out.write("         memcpy((char*)(&(s->" + id_array + "[" + first_id_array + "[" + one + "]])), (char*)(&(s->" + id_array + "[" + first_id_array + "[" + two + "]]))," + numberOfIdVariables + "*sizeof(uchar));\n");
		out.write("         memcpy((char*)(&(s->" + id_array + "[" + first_id_array + "[" + two + "]])), (char*)" + tempName + ", " + numberOfIdVariables + "*sizeof(uchar));\n");
	}
	
	private int firstChannelIdForChannel(int oneChannelId) {
		int result = firstChannelIdForProcess(typeInfo.getNoProcesses()-1) + numberOfChannelVariablesForProcess[typeInfo.getNoProcesses()-1];
		for(int i=0; i<oneChannelId; i++) {
			result += numberOfChannelVariablesForChannel[i];
		}
		return result;
	}

	private int firstProcessIdForChannel(int oneChannelId) {
		int result = firstProcessIdForProcess(typeInfo.getNoProcesses()-1) + numberOfPidVariablesForProcess[typeInfo.getNoProcesses()-1];
		for(int i=0; i<oneChannelId; i++) {
			result += numberOfPidVariablesForChannel[i];
		}
		return result;
	}

	private int firstChannelIdForProcess(int j) {
		int result = 0;
		for(int i=0; i<j; i++) {
			result += numberOfChannelVariablesForProcess[i];
		}
		return result;
	}

	private int firstProcessIdForProcess(int j) {
		int result = numberOfGlobalPidVariables;
		for(int i=0; i<j; i++) {
			result += numberOfPidVariablesForProcess[i];
		}
		return result;
	}


	
}
