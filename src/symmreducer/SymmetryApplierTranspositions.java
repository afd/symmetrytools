package src.symmreducer;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import junit.framework.Assert;
import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.Type;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.Strategy;

public class SymmetryApplierTranspositions extends SymmetryApplier {

	public SymmetryApplierTranspositions(StaticChannelDiagramExtractor typeInfo) {
		super(typeInfo);
	}
	
	public void applySymmetry(String fileName) {
		try {

			List<String> lines = readInput(fileName);
			writeOutputWithSymmetryReduction(fileName, lines);

		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
	}

	private void writeOutputWithSymmetryReduction(String fileName, List<String> lines) throws IOException {
		
		FileWriter fw = new FileWriter(fileName);
		boolean writtenApplyPrSwapToState = false;
		boolean writtenApplyChSwapToState = false;
		boolean writtenLt = false;
		boolean writtenFlatten = false;

		Assert.assertFalse(Config.REDUCTION_STRATEGY==Strategy.APPROXMARKERS);
		
		if(Config.REDUCTION_STRATEGY==Strategy.EXACTMARKERS) {
			for (int i = 0; i < lines.size(); i++) {
				if (lines.get(i).indexOf("JAVA") != -1) {
					writeApplyPrSwapToState(fw);
				} else if(lines.get(i).indexOf("MARKER") != -1) {
					writeMarkers(fw);
				} else {
					fw.write((String) lines.get(i) + "\n");
				}
			}
			fw.close();
			return;
		}

		for (int i = 0; i < lines.size(); i++) {
			if (lines.get(i).indexOf("JAVA") != -1) {
				if(!writtenApplyPrSwapToState) {
					writeApplyPrSwapToState(fw);
					writtenApplyPrSwapToState = true;	
				} else if(!writtenApplyChSwapToState) {
					writeApplyChSwapToState(fw);
					writtenApplyChSwapToState = true;
				} else if(Config.REDUCTION_STRATEGY==Strategy.FLATTEN && !writtenFlatten) {
					writeFlatten(fw);
					writtenFlatten = true;
				} else if(Config.REDUCTION_STRATEGY==Strategy.SEGMENT && !writtenLt) {
					writeLt(fw);
					writtenLt = true;
				} else {
					Assert.assertEquals(Config.REDUCTION_STRATEGY,Strategy.SEGMENT);
					writeConstructPartition(fw);
				}
			} else if(((String) lines.get(i)).indexOf("EQUAL METHODS") != -1) {
				Assert.assertEquals(Config.REDUCTION_STRATEGY,Strategy.SEGMENT);
				writeEqualProcesses(fw);
				writeEqualChannels(fw);
				writeGlobalVariablesForPartitionConstruction(fw);
			} else {
				fw.write((String) lines.get(i) + "\n");
			}
		}
		fw.close();
	}

	private void writeFlatten(FileWriter fw) throws IOException {
		writeFlattenSensitiveGlobals(fw);
		writeFlattenSensitiveLocals(fw);
		writeFlattenSensitiveChannels(fw);
	}

	private void writeFlattenSensitiveChannels(FileWriter fw) throws IOException {
		for(int i=0; i<typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(i))).getType();
			
			List<Type> flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
			
			if(containsPidType(flattenedFieldTypes)||containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q"+(i+1)+" *)QSEG(s,"+i+"))->Qlen; slot++) {\n");

				for(int j=0; j<flattenedFieldTypes.size(); j++) {
					if(isPid(flattenedFieldTypes.get(j))||isChan(flattenedFieldTypes.get(j))) {
						fw.write("      ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "=0;\n");
					}
				}
				fw.write("   }\n\n");
			}
		}
	}

	private void writeFlattenSensitiveLocals(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			String referencePrefix = "((P"+proctypeId(proctypeName)+" *)SEG(s,"+j+"))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToFlatten = new ArrayList<SensitiveVariableReference>();
			
			Map<String,EnvEntry> localScope = proctype.getLocalScope();
			for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if(localScope.get(varName) instanceof VarEntry) {
					referencesToFlatten.addAll(getSensitiveVariableReferences(varName,((VarEntry)localScope.get(varName)).getType(),referencePrefix));
				}
			}
			
			for(ListIterator iter = referencesToFlatten.listIterator(); iter.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter.next();
				Assert.assertTrue(isPid(reference.getType())||isChan(reference.getType()));
				fw.write("   " + reference.getReference() + " = 0;\n");
			}
			
			fw.write("\n");
		}
	}

	private void writeFlattenSensitiveGlobals(FileWriter fw) throws IOException {
		Map<String,EnvEntry> globalVariables = typeInfo.getEnv().getTopEntries();

		String referencePrefix = "s->" ;
	
		for(Iterator<String> iter = globalVariables.keySet().iterator(); iter.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if((entry instanceof VarEntry) && !(((VarEntry)entry).isHidden()||entry instanceof ChannelEntry)) {
				List sensitiveReferences = getSensitiveVariableReferences(name,((VarEntry) entry).getType(),referencePrefix);
				for(int i=0; i<sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences.get(i);
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("   " + reference.getReference() + " = 0;\n");
				}
			}
		}
	}
	
	private void writeGlobalVariablesForPartitionConstruction(FileWriter fw) throws IOException {
		for(int i=0; i<typeInfo.getProctypeNames().size(); i++) {
			List<Integer> processIdsOfThisProctype = new ArrayList<Integer>();
			for(int j=0; j<typeInfo.getProcessEntries().size(); j++) {
				ProcessEntry process = (ProcessEntry) typeInfo.getProcessEntries().get(j);
				if(process.getProctypeName().equals(typeInfo.getProctypeNames().get(i))) {
					processIdsOfThisProctype.add(new Integer(j+1));
				}
			}
			
			fw.write("int no_P" + i + " = " + processIdsOfThisProctype.size() + ";\n");
			fw.write("int P" + i + "_procs[" + processIdsOfThisProctype.size() + "] = { ");
			for(int j=0; j<processIdsOfThisProctype.size(); j++) {
				fw.write(processIdsOfThisProctype.get(j).toString());
				if(j<processIdsOfThisProctype.size()-1) {
					fw.write(", ");
				}
			}
			fw.write(" };\n\n");
		}

		int i=0;
		for(Iterator iter = typeInfo.getDistinctChannelSignatures().iterator(); iter.hasNext(); i++) {
			ChannelEntry channelSignature = (ChannelEntry) iter.next();
			List<Integer> channelsOfThisSignature = new ArrayList<Integer>();
			for(int j=0; j<typeInfo.getStaticChannelNames().size(); j++) {
				ChannelEntry channel = (ChannelEntry) typeInfo.getEnvEntry((String) typeInfo.getStaticChannelNames().get(j));
				if(channel.equal(channelSignature)) {
					channelsOfThisSignature.add(new Integer(j));
				}
			}
			
			fw.write("int no_Chantype" + i + " = " + channelsOfThisSignature.size() + ";\n");
			fw.write("int chantype" + i + "_chans[" + channelsOfThisSignature.size() + "] = { ");
			for(int j=0; j<channelsOfThisSignature.size(); j++) {
				fw.write(channelsOfThisSignature.get(j).toString());
				if(j<channelsOfThisSignature.size()-1) {
					fw.write(", ");
				}
			}
			fw.write(" };\n\n");
		}

	}

	private void writeConstructPartition(FileWriter fw) throws IOException {
		
		for(int i=0; i<typeInfo.getProctypeNames().size(); i++) {
			fw.write("  for(i=0; i<no_P" + i + "; i++) {\n");
			fw.write("    if(processClasses[P" + i + "_procs[i]]==-1) {\n");
			fw.write("      sprintf(temp,\"%d\",P" + i + "_procs[i]);\n");
			fw.write("      strcat(result,\"|\");\n");
			fw.write("      strcat(result,temp);\n\n");

			fw.write("      processClasses[P" + i + "_procs[i]]=++noProcessClasses;\n");
			fw.write("      int j;\n");
			fw.write("      for(j=i+1; j<no_P" + i + "; j++) {\n");
			fw.write("        if(equalProcesses(SEG(s,P" + i + "_procs[i]),SEG(s,P" + i + "_procs[j])," + i + ")) {\n");
			fw.write("          processClasses[P" + i + "_procs[j]] = noProcessClasses;\n");
			fw.write("          strcat(result,\",\");\n");
			fw.write("          sprintf(temp,\"%d\",P" + i + "_procs[j]);\n");
			fw.write("          strcat(result,temp);\n");
			fw.write("        }\n");
			fw.write("      }\n");
			fw.write("    }\n");
			fw.write("  }\n\n");
		}
		

		
		
		
		for(int i=0; i<typeInfo.getDistinctChannelSignatures().size(); i++) {
			fw.write("  for(i=0; i<no_Chantype" + i + "; i++) {\n");
			fw.write("    if(channelClasses[chantype" + i + "_chans[i]]==-1) {\n");
			fw.write("      sprintf(temp,\"%d\",chantype" + i + "_chans[i]+NO_PROCS);\n");
			fw.write("      strcat(result,\"|\");\n");
			fw.write("      strcat(result,temp);\n\n");

			fw.write("      channelClasses[chantype" + i + "_chans[i]]=++noChannelClasses;\n");
			fw.write("      int j;\n");
			
			fw.write("      for(j=i+1; j<no_Chantype" + i + "; j++) {\n");
			fw.write("        if(equalChannels(QSEG(s,chantype" + i + "_chans[i]),QSEG(s,chantype" + i + "_chans[j]),chantype" + i + "_chans[i] + 1" + ")) {\n");
			fw.write("          channelClasses[chantype" + i + "_chans[j]] = noChannelClasses;\n");
			fw.write("          strcat(result,\",\");\n");
			fw.write("          sprintf(temp,\"%d\",chantype" + i + "_chans[j]+NO_PROCS);\n");
			fw.write("          strcat(result,temp);\n");
			fw.write("        }\n");
			fw.write("      }\n");
			fw.write("    }\n");
			fw.write("  }\n\n");
		}

		
	}

	private void writeEqualChannels(FileWriter fw) throws IOException {

		fw.write("int equalChannels(void* q1, void* q2, int qt) {");
		fw.write("   int slot;\n\n");
		fw.write("   switch(qt) {\n");
		for(int i=1; i<=typeInfo.getStaticChannelNames().size(); i++) {
			String q1Prefix = "((Q" + i + "*)q1)->";
			String q2Prefix = "((Q" + i + "*)q2)->";

			fw.write("      case " + i + ": if(" + q1Prefix + "Qlen!=" + q2Prefix + "Qlen) return 0;\n");

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(i-1))).getType();
			List flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
		
			if(containsInsensitiveType(flattenedFieldTypes)) {
			
				fw.write("        for(slot=0; slot<((Q" + i +"*)q1)->Qlen; slot++) {\n\n");

				for(int k=0; k<flattenedFieldTypes.size(); k++) {
					if(! (isChan((Type) flattenedFieldTypes.get(k))|| isPid((Type) flattenedFieldTypes.get(k)))) {
						fw.write("          if(" + q1Prefix + "contents[slot].fld" + k + "!=" + q2Prefix + "contents[slot].fld" + k + ") return 0;\n");
					}
				}
				fw.write("        }\n");
			}
			fw.write("        return 1;\n");
		}

		fw.write("  }\n\n");
		fw.write("  printf(\"Error in channel comparison\\n\");\n\n");
		fw.write("  return 0;\n\n");
		fw.write("}\n\n");
	
	}

	private void writeEqualProcesses(FileWriter fw) throws IOException {
		fw.write("int equalProcesses(void* p1, void* p2, int pt) {");
		fw.write("   switch(pt) {\n");
		for(int i=0; i<typeInfo.getProctypeNames().size(); i++) {
			fw.write("      case " + i + ": return ((P" + i + "*)p1)->_p==((P" + i + "*)p2)->_p");

			List<String> referencesToCompare = new ArrayList<String>();
			
			ProctypeEntry proctype = (ProctypeEntry)typeInfo.getEnvEntry((String)typeInfo.getProctypeNames().get(i));

			Map<String,EnvEntry> localScope = proctype.getLocalScope();
			for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if(localScope.get(varName) instanceof VarEntry) {
					referencesToCompare.addAll(getInsensitiveVariableReferences(varName,((VarEntry)localScope.get(varName)).getType(),""));
				}
			}

			for(ListIterator iter = referencesToCompare.listIterator(); iter.hasNext(); ) {
				String reference = (String)iter.next();
				fw.write(" && ((P" + i + "*)p1)->" + reference + "==((P" + i + "*)p2)->" + reference);
			}

			fw.write(";\n");

		}
		
		fw.write("  }\n\n");
		fw.write("  printf(\"Error in process comparison\\n\");\n\n");
		fw.write("  return 0;\n\n");
		fw.write("}\n\n");
		
	}

	private void writeApplyChSwapToState(FileWriter fw) throws IOException {
		fw.write("   uchar tempCid;\n");
		fw.write("   int slot;\n");
		swapProctypeLocalChVariables(fw);
		swapChannelChContents(fw);
		swapChannels(fw);
	}

	private void writeApplyPrSwapToState(FileWriter fw) throws IOException {
		fw.write("   uchar tempPid;\n");
		fw.write("   int slot;\n");
		
		swapPrGlobal(fw);
		swapProctypeLocalPrVariables(fw);
		swapChannelPrContents(fw);
		swapProcesses(fw);
	}

	private void swapPrGlobal(FileWriter fw) throws IOException {
		Map<String,EnvEntry> globalVariables = typeInfo.getEnv().getTopEntries();

		String referencePrefix = "s->" ;
		
		for(Iterator<String> iter = globalVariables.keySet().iterator(); iter.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if((entry instanceof VarEntry) && !(((VarEntry)entry).isHidden()||entry instanceof ChannelEntry)) {
				List sensitiveReferences = getSensitiveVariableReferences(name,((VarEntry)entry).getType(),referencePrefix);
				for(int i=0; i<sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences.get(i);
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("   if(" + reference.getReference() + "==a) {\n");
					fw.write("      " + reference.getReference() + " = b;\n");
					fw.write("   } else if(" + reference.getReference() + "==b) {\n");
					fw.write("      " + reference.getReference() + " = a;\n");
					fw.write("   }\n");
				}
				
				List sensitivelyIndexedArrays = getSensitivelyIndexedArrayReferences(name,((VarEntry)entry).getType(),referencePrefix);
				for(int i=0; i<sensitivelyIndexedArrays.size(); i++) {
					PidIndexedArrayReference reference = (PidIndexedArrayReference) sensitivelyIndexedArrays.get(i);
					Assert.assertTrue(isPid(((ArrayType)reference.getType()).getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar temp;\n");
					fw.write("       temp = " + reference.getReference() + "[a];\n");
					fw.write("       " + reference.getReference() + "[a] = " + reference.getReference() + "[b];\n");
					fw.write("       " + reference.getReference() + "[b] = temp;\n");
					fw.write("   }\n");
				}
			}
		}
	}

	private void writeLt(FileWriter fw) throws IOException {
		fw.write("  int slot;\n\n");
	
		for (int j=0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			String sPrefix = "((P" + proctypeId(proctypeName) + " *)SEG(s," + j + "))->";
			String tPrefix = "((P" + proctypeId(proctypeName) + " *)SEG(t," + j + "))->";
			ProctypeEntry proctype = (ProctypeEntry) typeInfo.getEnvEntry(proctypeName);

			fw.write("  if(" + sPrefix + "_p < " + tPrefix + "_p) return 1;\n");
			fw.write("  if(" + sPrefix + "_p > " + tPrefix + "_p) return 0;\n\n");

			List<String> referencesToCompare = new ArrayList<String>();
			
			Map<String,EnvEntry> localScope = proctype.getLocalScope();
			for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if(localScope.get(varName) instanceof VarEntry) {
					referencesToCompare.addAll(getInsensitiveVariableReferences(varName,((VarEntry)localScope.get(varName)).getType(),""));
				}
			}

			for(ListIterator iter = referencesToCompare.listIterator(); iter.hasNext(); ) {
				String reference = (String)iter.next();
				fw.write("  if(" + sPrefix + reference + " < " + tPrefix + reference + ") return 1;\n");
				fw.write("  if(" + sPrefix + reference + " > " + tPrefix + reference + ") return 0;\n\n");
			}
		}
		
		for(int j=0; j<typeInfo.getStaticChannelNames().size(); j++) {

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(j))).getType();
			List flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
			
			String sPrefix = "((Q" + (j+1)+" *)QSEG(s,"+j+"))->";
			String tPrefix = "((Q" + (j+1)+" *)QSEG(t,"+j+"))->";

			fw.write("  if(" + sPrefix + "Qlen < " + tPrefix + "Qlen) return 1;\n");
			fw.write("  if(" + sPrefix + "Qlen > " + tPrefix + "Qlen) return 0;\n\n");
			
			if(containsInsensitiveType(flattenedFieldTypes)) {
			
				fw.write("  for(slot=0; slot<((Q"+(j+1)+" *)QSEG(s,"+j+"))->Qlen; slot++) {\n\n");

				for(int k=0; k<flattenedFieldTypes.size(); k++) {
					if(! (isChan((Type) flattenedFieldTypes.get(k))|| isPid((Type) flattenedFieldTypes.get(k)))) {
						fw.write("    if(" + sPrefix + "contents[slot].fld" + k + " < " + tPrefix + "contents[slot].fld" + k + ") return 1;\n");
						fw.write("    if(" + sPrefix + "contents[slot].fld" + k + " > " + tPrefix + "contents[slot].fld" + k + ") return 0;\n\n");
					}
				}
			
				fw.write("   }\n\n");
			}
		}
		
	}

	private void swapProctypeLocalPrVariables(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			String referencePrefix = "((P"+proctypeId(proctypeName)+" *)SEG(s,"+j+"))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();
			List<SensitiveVariableReference> sensitivelyIndexedArrays = new ArrayList<SensitiveVariableReference>();			
			
			Map<String,EnvEntry> localScope = proctype.getLocalScope();
			for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if(localScope.get(varName) instanceof VarEntry) {
					referencesToPermute.addAll(getSensitiveVariableReferences(varName,((VarEntry)localScope.get(varName)).getType(),referencePrefix));
					sensitivelyIndexedArrays.addAll(getSensitivelyIndexedArrayReferences(varName,((VarEntry)localScope.get(varName)).getType(),referencePrefix));
				}
			}
			
			for(ListIterator iter = referencesToPermute.listIterator(); iter.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter.next();
				Assert.assertTrue(isPid(reference.getType())||isChan(reference.getType()));
				if(isPid(reference.getType())) {
					fw.write("   if(" + reference.getReference() + "==a) {\n");
					fw.write("   " + reference.getReference() + " = b;\n");
					fw.write("   } else if(" + reference.getReference() + "==b) {\n");
					fw.write("   " + reference.getReference() + " = a;\n");
					fw.write("   }\n");
				} 
			}
			
			for(ListIterator iter = sensitivelyIndexedArrays.listIterator(); iter.hasNext();) {
				PidIndexedArrayReference reference = (PidIndexedArrayReference) iter.next();
				Assert.assertTrue(isPid(((ArrayType)reference.getType()).getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar temp;\n");
				fw.write("       temp = " + reference.getReference() + "[a];\n");
				fw.write("       " + reference.getReference() + "[a] = " + reference.getReference() + "[b];\n");
				fw.write("       " + reference.getReference() + "[b] = temp;\n");
				fw.write("   }\n");
			}
			
			fw.write("\n");
		}
		
	}

	private void swapChannelChContents(FileWriter fw) throws IOException {
		for(int i=0; i<typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(i))).getType();
			
			List flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
			
			if(containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q"+(i+1)+" *)QSEG(s,"+i+"))->Qlen; slot++) {\n");

				for(int j=0; j<flattenedFieldTypes.size(); j++) {
					if(isChan((Type) flattenedFieldTypes.get(j))) {
						fw.write("      if(((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "==a+1) {\n");
						fw.write("         ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "=b+1;\n");
						fw.write("      } else if(((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "==b+1) {\n");
						fw.write("         ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "=a+1;\n");
						fw.write("      }\n");
					}
				}
				fw.write("   }\n");
			}
		}
		
	}
	
	private void swapChannelPrContents(FileWriter fw) throws IOException {
		
		for(int i=0; i<typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(i))).getType();
			
			List flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
			
			if(containsPidType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q"+(i+1)+" *)QSEG(s,"+i+"))->Qlen; slot++) {\n");

				for(int j=0; j<flattenedFieldTypes.size(); j++) {
					if(isPid((Type) flattenedFieldTypes.get(j))) {
						fw.write("      if(((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "==a) {\n");
						fw.write("         ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "=b;\n");
						fw.write("      } else if(((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "==b) {\n");
						fw.write("         ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ "=a;\n");
						fw.write("      }\n");
					}
				}
				fw.write("   }\n");
			}
		}
		
	}
	
	private void swapProctypeLocalChVariables(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			String referencePrefix = "((P"+proctypeId(proctypeName)+" *)SEG(s,"+j+"))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();

			
			Map<String,EnvEntry> localScope = proctype.getLocalScope();
			for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
				String varName = iter.next();
				if(localScope.get(varName) instanceof VarEntry) {
					referencesToPermute.addAll(getSensitiveVariableReferences(varName,((VarEntry)localScope.get(varName)).getType(),referencePrefix));
				}
			}
			
			for(ListIterator iter = referencesToPermute.listIterator(); iter.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter.next();
				Assert.assertTrue(isPid(reference.getType())||isChan(reference.getType()));
				if(isChan(reference.getType())) {
					fw.write("   if(" + reference.getReference() + "==a+1) {\n");
					fw.write("      " + reference.getReference() + " = b+1;\n");
					fw.write("   } else if(" + reference.getReference() + "==b+1) {\n");
					fw.write("      " + reference.getReference() + " = a+1;\n");
					fw.write("   }\n");
				}
			}
		
			fw.write("\n");
			
		}
		
	}

	private boolean containsPidType(List flattenedFieldTypes) {
		for(int i=0; i<flattenedFieldTypes.size(); i++) {
			if(isPid((Type) flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	private boolean containsChanType(List flattenedFieldTypes) {
		for(int i=0; i<flattenedFieldTypes.size(); i++) {
			if(isChan((Type) flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	private boolean containsInsensitiveType(List flattenedFieldTypes) {
		for(int i=0; i<flattenedFieldTypes.size(); i++) {
			if(! (isPid((Type) flattenedFieldTypes.get(i)) || isChan((Type) flattenedFieldTypes.get(i)))) {
				return true;
			}
		}
		return false;
	}
	
	private void swapProcesses(FileWriter fw) throws IOException {
		for (int j = 1; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			int proctypeIdentifier = proctypeId(proctypeName);
			fw.write("   if(a==" + j + ") {\n");
			fw.write("      P" + proctypeIdentifier + " temp;\n");
			fw.write("      memcpy(&temp,SEG(s,a),sizeof(P" + proctypeIdentifier + "));\n");
			fw.write("      memcpy(SEG(s,a),SEG(s,b),sizeof(P" + proctypeIdentifier + "));\n");
			fw.write("      memcpy(SEG(s,b),&temp,sizeof(P" + proctypeIdentifier + "));\n");
			fw.write("      tempPid = VAR(s,a,_pid,P" + proctypeIdentifier + ");\n");
			fw.write("      VAR(s,a,_pid,P" + proctypeIdentifier + ") = VAR(s,b,_pid,P" + proctypeIdentifier + ");\n");
			fw.write("      VAR(s,b,_pid,P" + proctypeIdentifier + ") = tempPid;\n");
			fw.write("      return;\n");
			fw.write("   }\n\n");
		}
	}

	private void swapChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {
			int chantypeIdentifier = j+1;
			fw.write("   if(a==" + j + ") {\n");
			fw.write("      Q" + chantypeIdentifier + " temp;\n");
			fw.write("      memcpy(&temp,QSEG(s,a),sizeof(Q"+chantypeIdentifier+"));\n");
			fw.write("      memcpy(QSEG(s,a),QSEG(s,b),sizeof(Q"+chantypeIdentifier+"));\n");
			fw.write("      memcpy(QSEG(s,b),&temp,sizeof(Q"+chantypeIdentifier+"));\n");
			fw.write("      tempCid = QVAR(s,a,_t,Q"+chantypeIdentifier+");\n");
			fw.write("      QVAR(s,a,_t,Q"+chantypeIdentifier+") = QVAR(s,b,_t,Q"+chantypeIdentifier+");\n");
			fw.write("      QVAR(s,b,_t,Q"+chantypeIdentifier+") = tempCid;\n");
			fw.write("   };\n");
			fw.write("\n");
		}
	}

	private List<String> readInput(String fileName) throws FileNotFoundException,
			IOException {
		List<String> lines = new ArrayList<String>();
		BufferedReader br = new BufferedReader(new FileReader(fileName));
		String str;
		while ((str = br.readLine()) != null) {
			lines.add(str);
		}
		br.close();
		return lines;
	}

}
