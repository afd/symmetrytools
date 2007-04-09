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
import src.etch.types.ChanType;
import src.etch.types.Type;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.Strategy;

public class SymmetryApplierBasic extends SymmetryApplier {

	public SymmetryApplierBasic(StaticChannelDiagramExtractor typeInfo) {
		super(typeInfo);
		if(Config.REDUCTION_STRATEGY==Strategy.SEGMENT) {
			System.out.println("Segmented strategy not yet supported without transpositions");
			System.exit(0);
		}
		if(Config.REDUCTION_STRATEGY==Strategy.FLATTEN) {
			System.out.println("Approximate verification using symmetry markers not yet supported without transpositions");
			System.exit(0);
		}

		Assert.assertFalse(Config.REDUCTION_STRATEGY==Strategy.EXACTMARKERS);
		Assert.assertFalse(Config.REDUCTION_STRATEGY==Strategy.APPROXMARKERS);
		Assert.assertFalse(Config.REDUCTION_STRATEGY==Strategy.BOSNACKIMARKERS);
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
		for (int i = 0; i < lines.size(); i++) {
			if (lines.get(i).indexOf("JAVA") != -1) {
				writeApplyPermToState(fw);
			} else {
				fw.write((String) lines.get(i) + "\n");
			}
		}
		fw.close();
	}

	private void writeApplyPermToState(FileWriter fw) throws IOException {
		permuteGlobalVariables(fw);
		permuteProctypeLocalVariables(fw);
		permuteChannelContents(fw);
		permuteProcesses(fw);
		permuteChannels(fw);
	}
	
	
	private void permuteGlobalVariables(FileWriter fw) throws IOException {
		Map<String,EnvEntry> globalVariables = typeInfo.getEnv().getTopEntries();

		for(Iterator<String> iter = globalVariables.keySet().iterator(); iter.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if((entry instanceof VarEntry) && !(((VarEntry)entry).isHidden()||entry instanceof ChannelEntry)) {
				List sensitiveReferences = getSensitiveVariableReferences(name,((VarEntry)entry).getType(),"");
				for(int i=0; i<sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences.get(i);
					fw.write("   temp->" + reference.getReference() + " = ");
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("applyToPr(*alpha,s->"+reference.getReference()+");\n");
				}
				
				List sensitivelyIndexedArrays = getSensitivelyIndexedArrayReferences(name,((VarEntry)entry).getType(),"");
				for(int i=0; i<sensitivelyIndexedArrays.size(); i++) {
					PidIndexedArrayReference reference = (PidIndexedArrayReference) sensitivelyIndexedArrays.get(i);
					Assert.assertTrue(isPid(((ArrayType)reference.getType()).getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar swapper[" + reference.getArrayLength() + "];\n");
					fw.write("       for(j=0; j<" + reference.getArrayLength() + "; j++) {\n");
					fw.write("          temp->" + reference.getReference() + "[applyToPr(*alpha,j)] = s->" + reference.getReference() + "[j];\n");
					fw.write("       }");
					fw.write("   }\n");
				}
			}
		}
	}

	private void permuteProctypeLocalVariables(FileWriter fw) throws IOException {
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
				fw.write("   " + reference.getReference() + " = ");

				Assert.assertTrue(isPid(reference.getType())||isChan(reference.getType()));
				if(isPid(reference.getType())) {
					fw.write("applyToPr");
				} else {
					fw.write("applyToCh");
				}
				fw.write("(*alpha,"+reference.getReference());
				if(isChan(reference.getType())) {
					fw.write("-1)+1;\n");
				} else {
					fw.write(");\n");
				}
				
			}
			
			for(ListIterator iter = sensitivelyIndexedArrays.listIterator(); iter.hasNext();) {
				PidIndexedArrayReference reference = (PidIndexedArrayReference) iter.next();
				Assert.assertTrue(isPid(((ArrayType)reference.getType()).getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar swapper[" + reference.getArrayLength() + "];\n");
				fw.write("       for(j=0; j<" + reference.getArrayLength() + "; j++) {\n");
				fw.write("          swapper[applyToPr(*alpha,j)] = " + reference.getReference() + "[j];\n");
				fw.write("       }");
				fw.write("       memcpy("+reference.getReference()+",swapper,"+reference.getArrayLength()+"*sizeof(uchar));\n");
				fw.write("   }\n");
				
			}
			
			fw.write("\n");
		}
	}

	private void permuteChannelContents(FileWriter fw) throws IOException {

		for(int i=0; i<typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry)typeInfo.getEnvEntry((String)typeInfo.getStaticChannelNames().get(i))).getType();
			
			List flattenedFieldTypes = TypeFlattener.flatten(type.getMessageType(),typeInfo);
			
			if(containsSensitiveType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q"+(i+1)+" *)QSEG(s,"+i+"))->Qlen; slot++) {\n");

				for(int j=0; j<flattenedFieldTypes.size(); j++) {
					if(isPid((Type) flattenedFieldTypes.get(j))||isChan((Type) flattenedFieldTypes.get(j))) {
						fw.write("      ((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j+ " = ");
						if(isPid((Type) flattenedFieldTypes.get(j))) {
							fw.write("applyToPr");
						} else {
							Assert.assertTrue(isChan((Type)flattenedFieldTypes.get(j)));
							fw.write("applyToCh");
						}
						fw.write("(*alpha,((Q"+(i+1)+" *)QSEG(s,"+i+"))->contents[slot].fld"+j);
						if(isChan((Type) flattenedFieldTypes.get(j))) {
							fw.write("-1)+1;\n");
						} else {
							Assert.assertTrue(isPid((Type)flattenedFieldTypes.get(j)));
							fw.write(");\n");
						}
					}
				}
				fw.write("   }\n");
			}
		}
	}

	private boolean containsSensitiveType(List flattenedFieldTypes) {
		for(int i=0; i<flattenedFieldTypes.size(); i++) {
			if(isChan((Type) flattenedFieldTypes.get(i))||isPid((Type) flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	private void permuteProcesses(FileWriter fw) throws IOException {
		for (int j = 1; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry)typeInfo.getProcessEntries().get(j)).getProctypeName();
			int proctypeIdentifier = proctypeId(proctypeName);
			fw.write("   j = applyToPr(*alpha," + j + ");\n");
			fw.write("   memcpy(SEG(temp,j),SEG(s," + j
					+ "),sizeof(P" + proctypeIdentifier + "));\n");
			fw.write("   VAR(temp,j,_pid,P" + proctypeIdentifier
					+ ")=VAR(s,j,_pid,P" + proctypeIdentifier
					+ ");\n");
			fw.write("\n");
		}
	}

	private void permuteChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {
			int chantypeIdentifier = j+1;
			fw.write("   j = applyToCh(*alpha," + j + ");\n");
			fw.write("   memcpy(QSEG(temp,j),QSEG(s," + j
					+ "),sizeof(Q" + chantypeIdentifier + "));\n");
			fw.write("   QVAR(temp,j,_t,Q" + chantypeIdentifier
					+ ")=QVAR(s,j,_t,Q" + chantypeIdentifier
					+ ");\n");
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
