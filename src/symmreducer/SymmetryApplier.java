package src.symmreducer;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;

import junit.framework.Assert;
import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.SimpleType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmreducer.strategies.BasicEnumeration;
import src.symmreducer.strategies.Flatten;
import src.symmreducer.strategies.LocalSearch;
import src.symmreducer.strategies.Markers;
import src.symmreducer.strategies.MinimisingSet;
import src.symmreducer.strategies.StabiliserChainEnumeration;
import src.utilities.Config;
import src.utilities.FileManager;
import src.utilities.ProgressPrinter;
import src.utilities.Strategy;
import src.utilities.StringHelper;

public class SymmetryApplier {

	SwapVectorizer swapVectorizer = null;
	
	public static String stateType;

	public static String memoryCopy;

	public static String memoryCompare;

	protected StaticChannelDiagramExtractor typeInfo;

	private String specification;

	private String groupGenerators;

	private FileWriter symmetryGroupFile;

	private FileWriter permutationFile;
	
	public SymmetryApplier(String specification,
			StaticChannelDiagramExtractor typeInfo, String groupGenerators) {
		this.specification = specification;
		this.typeInfo = typeInfo;
		this.groupGenerators = groupGenerators;

		stateType = Config.VECTORIZE_ID_SWAPPING ? "AugmentedState" : "State";

		memoryCopy = Config.VECTORIZE_ID_SWAPPING ? "augmented_memcpy" : "memcpy";
		memoryCompare = Config.VECTORIZE_ID_SWAPPING ? "augmented_memcmp" : "memcmp";
		
	}

	public void applySymmetry() {
		try {
			createHeaderFileToContainGroupElements();
			createHeaderFileToContainPermutationCode();
			generatePanFiles();
			dealWithSympanHeader();
			dealWithSympanBody();
			dealWithGroupFiles();
			dealWithSegmentFiles();
			symmetryGroupFile.close();
			permutationFile.close();
		} catch (Exception e) {
			System.out
					.println("An error occurred while constructing the \"sympan\" files.");
			e.printStackTrace();
			System.exit(1);
		}
	}

	private void createHeaderFileToContainPermutationCode() throws IOException {
	    permutationFile = new FileWriter("apply_permutation.h");
	}

	private void createHeaderFileToContainGroupElements() throws IOException {
	    symmetryGroupFile = new FileWriter("symmetry_group.h");
	}

	private void dealWithSympanBody() throws IOException {
		List<String> groupInfo = null;

		if(!usingMarkers()) {
			groupInfo = readFile("groupinfo");
		}

		List<String> lines = readFile("sympan.c");
		FileWriter out = new FileWriter("sympan.c");


		for (int counter = 0; counter < lines.size(); counter++) {

			if (lineInvolvesHashStore(lines, counter)) {
				replaceWithRepresentativeStore(lines, counter);
			}

			/* #include "pan.h" becomes #include "sympan.h" */
			lines.set(counter, lines.get(counter).replace("#include \"pan.h\"",
					"#include \"sympan.h\""));
			writeln(out, lines.get(counter));

			if (lines.get(counter).contains("sympan.h")) {
				// Once the line which includes "sympan.h" has been dealt
				// with, include all the symmetry stuff
				out.write("/* ADDED FOR SYMMETRY */\n\n");

				writePreprocessorMacros(out);

				if(Config.VECTORIZE_ID_SWAPPING) {
					swapVectorizer = new SwapVectorizer(typeInfo);
					swapVectorizer.writeIdSwappingDataStructuresAndProcedures(out);
				}

				writeMinNow(out);

				out.write("#include \"apply_permutation.h\"\n");
				
				if (Config.USE_TRANSPOSITIONS) {

					writeApplyPrSwapToState();

					if (!usingMarkers()) {
						writeApplyChSwapToState();
						writeApplyPermToStateTranspositions();
					}
				} else if (!usingMarkers()) {
					writeApplyPermToStateBasic(out);
				}

				writeParallelIncludeLines(out);
				
				if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
					writeLt(out);
					writeEqualProcesses(out);
					writeEqualChannels(out);
					writeConstructPartition(out);
					out.write("#include \"segment.h\"\n");

				} else if (Config.REDUCTION_STRATEGY == Strategy.FLATTEN) {
					Flatten.writeFlatten(out, typeInfo);
				} else if (usingMarkers()) {
					Markers.writeMarkers(out, typeInfo);
				}

				if (!usingMarkers()) {
					writeGlobalVariablesForSymmetryGroups(groupInfo, out);
				}

				writeRepFunction(groupInfo, out);
			}

			if (verificationEndPoint(lines, counter)) {
				if(Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
					writeWrapUpSegment(out);
				}
				
			}

			if (!usingMarkers() && mainMethodReached(lines, counter)) {
				dealWithMainMethod(groupInfo, out);
			}
		}
		out.close();
	}
	
	protected void writeParallelIncludeLines(FileWriter out) throws IOException {
		// Overridden by parallel symmetry applier
	}

	private void writeMinNow(FileWriter out) throws IOException {
		out.write(stateType + " min_now;\n\n");
	}

	protected void dealWithMainMethod(List<String> groupInfo, FileWriter out) throws IOException {
		/*
		 * When the main method is reached, add code to initialise
		 * symmetry group. If we're using markers don't do this.
		 */

		// LOOK IN THE GROUP INFO FILE AND FILL UP THE ARRAYS FOR
		// EACH SET
		if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
			writeSendGroupToGAP(out);
		}

		int setCounter = 0;
		int index = 0;

		symmetryGroupFile.write("\nstatic void initialiseGroup() {\n");

		out.write("   initialiseGroup();\n");
		
		for (int groupInfoCounter = 0; groupInfoCounter < groupInfo
				.size(); groupInfoCounter++) {

			if(groupInfo.get(groupInfoCounter).contains("parallel")) {
				continue;
			}
			
			// Sims method
			if (Config.USE_STABILISER_CHAIN
					&& groupInfo.get(groupInfoCounter).contains(
							"<enumerate>")) {
				groupInfoCounter = writeInstantiateStabiliserChain(
						groupInfo, setCounter, groupInfoCounter);
			} else {
				if (groupInfo.get(groupInfoCounter).contains("<")) {
					// skip the line which says how many
					// permutations there will be
					groupInfoCounter++;
					setCounter++;
					index = 0;
				} else {
					groupInfoCounter = writeInstantiateElement(
							groupInfo, setCounter, index++,
							groupInfoCounter);
				}
			}
		}
		
		symmetryGroupFile.write("}\n");

	}

	private int writeInstantiateElement(List<String> groupInfo,
			int setCounter, int index, int groupInfoCounter) throws IOException {
		symmetryGroupFile.write("   elementset_" + setCounter + "[" + index
				+ "]=constructPerm(\"");
		String perm = groupInfo.get(groupInfoCounter);
		while (perm.contains("\\")) {
			perm = perm.substring(0, perm.length() - 2)
					+ groupInfo.get(++groupInfoCounter);
		}
		if (Config.USE_TRANSPOSITIONS) {
			symmetryGroupFile.write(StringHelper.trimWhitespace(perm));
		} else {
			symmetryGroupFile.write(convertPerm(StringHelper.trimWhitespace(perm)));
		}
		symmetryGroupFile.write("\");\n");
		return groupInfoCounter;
	}

	private int writeInstantiateStabiliserChain(List<String> groupInfo,
			int setCounter, int groupInfoCounter)
			throws IOException {
		setCounter++;

		int noPartitions = Integer.parseInt(StringHelper
				.trimWhitespace(groupInfo.get(groupInfoCounter + 1)));
		groupInfoCounter += 2;
		int partitionCounter = 0;
		while (partitionCounter < noPartitions) {
			String[] cosetInfo = groupInfo.get(groupInfoCounter).split(":");
			groupInfoCounter++;
			int partitionSize = Integer.parseInt(StringHelper
					.trimWhitespace(cosetInfo[1]));
			symmetryGroupFile.write("\n   elementset_" + setCounter + "[" + partitionCounter
					+ "] = malloc(" + partitionSize
					+ " * sizeof(perm_t));\n");
			if (Config.USE_TRANSPOSITIONS) {
				symmetryGroupFile.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][0] = constructPerm(\"\");\n");
			} else {
				symmetryGroupFile.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][0] = constructPerm(\"()\");\n");
			}
			for (int cosetrepCounter = 1; cosetrepCounter < partitionSize; cosetrepCounter++) {
				symmetryGroupFile.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][" + cosetrepCounter
						+ "] = constructPerm(\"");
				String perm = groupInfo.get(groupInfoCounter);
				while (perm.contains("\\")) {
					perm = perm.substring(0, perm.length() - 2)
							+ groupInfo.get(++groupInfoCounter);
				}
				if (Config.USE_TRANSPOSITIONS) {
					symmetryGroupFile.write(StringHelper.trimWhitespace(perm));
				} else {
					symmetryGroupFile.write(convertPerm(StringHelper.trimWhitespace(perm)));
				}
				symmetryGroupFile.write("\");\n");
				groupInfoCounter++;
			}
			partitionCounter++;
		}
		return groupInfoCounter;
	}

	private void writeSendGroupToGAP(FileWriter out) throws IOException {
		out.write("  printf(\"grp:Group(" + groupGenerators + ");\\n\");\n\n");
	}

	private void writeWrapUpSegment(FileWriter out) throws IOException {
		out
				.write("   printf(\"Number of stabilisers: %d\\n\",noStabilisers);\n");
		out.write("   printf(\"stp\\n\");\n");
	}

	private boolean verificationEndPoint(List<String> lines, int counter) {
		return lines.get(counter).contains("if (signoff)");
	}

	private void writeGlobalVariablesForSymmetryGroups(List<String> groupInfo,
			FileWriter out) throws IOException {

		out.write("#include \"symmetry_group.h\"\n\n");
		
		int setcounter = 1; // NOW LOOK IN THE GROUP INFO FILE
		// AND PUT THE APPROPRIATE
		// DECLARATIONS
		for (int groupInfoCounter = 0; groupInfoCounter < groupInfo.size(); groupInfoCounter++) {

			if(groupInfo.get(groupInfoCounter).contains("parallel")) {
				continue;
			}
			
			if (groupInfo.get(groupInfoCounter).contains("<")) {
				if (Config.USE_STABILISER_CHAIN
						&& groupInfo.get(groupInfoCounter).contains(
								"<enumerate>")) {
					symmetryGroupFile.write("static perm_t* elementset_");
				} else {
					symmetryGroupFile.write("static perm_t elementset_");
				}
				symmetryGroupFile.write(setcounter
						+ "["
						+ StringHelper.trimWhitespace(groupInfo
								.get(groupInfoCounter + 1)) + "];\n");
				setcounter++;
			}
		}
	}

	private boolean mainMethodReached(List<String> lines, int counter) {
		return lines.get(counter).contains("void to_compile(void);");
	}

	protected void writeRepFunction(List<String> groupInfo, FileWriter out)
			throws IOException {
		
		out.write("\nState *rep(State *orig_now) {\n\n");

		if (usingMarkers()) {
			Markers.writeRepFunction(typeInfo, out);
		} else {
			if(Config.VECTORIZE_ID_SWAPPING) {
				out.write("   memcpy(&(min_now.state),orig_now, vsize);\n");
				out.write("   extractIdentifierVariables(&min_now);\n");
			} else {
				out.write("   memcpy(&min_now,orig_now, vsize);\n");
			}
			// STRATEGIES GO HERE
			if (Config.REDUCTION_STRATEGY == Strategy.FLATTEN) {
				out.write("   flatten(&min_now);\n");
			}
			int groupInfoCounter = 0;
			int setCounter = 1;
			while (groupInfoCounter < groupInfo.size()) {

				// ENUMERATION STRATEGY WITH SIMS METHOD
				if (Config.USE_STABILISER_CHAIN
						&& groupInfo.get(groupInfoCounter).contains(
								"<enumerate>")) {
					groupInfoCounter = writeRepEnumerateStabiliserChain(
							groupInfo, out, groupInfoCounter, setCounter);
					setCounter++;
				}

				// BASIC ENUMERATION STRATEGY
				if (!Config.USE_STABILISER_CHAIN
						&& groupInfo.get(groupInfoCounter).contains(
								"<enumerate>")) {
					BasicEnumeration.writeRepFunction(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}
				
				// MINIMISING SET STRATEGY
				if (groupInfo.get(groupInfoCounter).contains("<minimise>")) {
					MinimisingSet.writeRep(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}

				// LOCAL SEARCH STRATEGY

				if (groupInfo.get(groupInfoCounter).contains("<localsearch>")) {
					LocalSearch.writeRep(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}

				groupInfoCounter++;
			}

			if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
				out.write("   segment(&min_now);\n\n");
			}

		}

		if(Config.VECTORIZE_ID_SWAPPING) {
			out.write("   replaceIdentifierVariables(&min_now);\n");
			out.write("   return &(min_now.state);\n");
		} else {
			out.write("   return &min_now;\n");
		}
		out.write("}\n\n");
	}

	private int writeRepEnumerateStabiliserChain(List<String> groupInfo,
			FileWriter out, int groupInfoCounter, int setCounter)
			throws IOException {
		final int stabiliserChainSize = StabiliserChainEnumeration.getSizeOfStabiliserChain(groupInfo, groupInfoCounter);
		List<Integer> stabiliserChainComponentSizes = StabiliserChainEnumeration.getStabiliserChainComponentSizes(groupInfo, groupInfoCounter, stabiliserChainSize);

		List<String> start = new ArrayList<String>();
		List<String> end = new ArrayList<String>();
		
		for(int i=0; i<stabiliserChainSize; i++) {
			start.add("0");
			end.add(stabiliserChainComponentSizes.get(i).toString());
		}
		
		out.write("   {\n");

		out.write("   " + stateType + " originalForThisStrategy;\n");
		out.write("   " + memoryCopy + "(&originalForThisStrategy,&min_now,vsize);\n\n");

		StabiliserChainEnumeration.outputSimsEnumeration(out, setCounter, stabiliserChainSize, start, end, "min_now", "&originalForThisStrategy");

		out.write("   } /* End of sims enumeration */\n");

		return newValueOfGroupInfoCounter(groupInfoCounter, groupInfo, stabiliserChainSize);

	}

	private int newValueOfGroupInfoCounter(int groupInfoCounter, List<String> groupInfo, int stabiliserChainSize) {
		int partitionCounter = 0;
		while(partitionCounter < stabiliserChainSize) {
			if (groupInfo.get(groupInfoCounter).contains("coset")) {
				partitionCounter++;
			}
			groupInfoCounter++;
		}
		return groupInfoCounter;
	}
	
	/* Methods to apply a permutation to a state, without transpositions */

	protected void writeApplyPermToStateBasic(FileWriter fw) throws IOException {
		fw.write("void applyPermToState(State *s, perm_t *alpha) {\n");
		fw.write("   int j, slot;\n");
		fw.write("   State temp;\n");
		fw.write("   memcpy(&temp, s, vsize);\n\n");
		permuteGlobalVariables(fw);
		permuteProctypeLocalVariables(fw);
		permuteChannelContents(fw);
		permuteProcesses(fw);
		permuteChannels(fw);
		fw.write("   memcpy(s,&temp,vsize);\n");
		fw.write("}\n\n");
	}

	private void permuteGlobalVariables(FileWriter fw) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List<SensitiveVariableReference> sensitiveReferences = SensitiveVariableReference.getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), "", typeInfo);
				for (SensitiveVariableReference reference : sensitiveReferences) {
					fw.write("   temp." + reference + " = ");
					Assert.assertTrue(PidType.isPid(reference.getType()));
					fw.write("applyToPr(*alpha,s->" + reference
							+ ");\n");
				}

				List<PidIndexedArrayReference> sensitivelyIndexedArrays = PidIndexedArrayReference.getSensitivelyIndexedArrayReferences(
						name, ((VarEntry) entry).getType(), "", typeInfo);
				for (PidIndexedArrayReference reference : sensitivelyIndexedArrays) {
					Assert.assertTrue(((ArrayType) reference.getType()).getIndexType() instanceof VisibleType);
					Assert.assertTrue(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
							.getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar swapper["
							+ reference.getArrayLength() + "];\n");
					fw.write("       for(j=0; j<" + reference.getArrayLength()
							+ "; j++) {\n");
					fw.write("          temp." + reference
							+ "[applyToPr(*alpha,j)] = s->"
							+ reference + "[j];\n");
					fw.write("       }");
					fw.write("   }\n");
				}
			}
		}
	}

	private void permuteProctypeLocalVariables(FileWriter fw)
			throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {

			String referencePrefix = "((P" + typeInfo.proctypeId(( typeInfo.getProcessEntries().get(j)).getProctypeName())
					+ " *)SEG(s," + j + "))->";

			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();
			List<SensitiveVariableReference> sensitivelyIndexedArrays = new ArrayList<SensitiveVariableReference>();

			for (Iterator<Entry<String,VisibleType>> iter = typeInfo.getProctypeEntryForProcess(j).variableTypePairIterator(); iter.hasNext(); ) {
				Entry<String,VisibleType> entry = iter.next();

				referencesToPermute.addAll(SensitiveVariableReference.getSensitiveVariableReferences(
						entry.getKey(), entry.getValue(), referencePrefix, typeInfo));
				sensitivelyIndexedArrays
						.addAll(PidIndexedArrayReference.getSensitivelyIndexedArrayReferences(
								entry.getKey(), entry.getValue(), referencePrefix, typeInfo));
			}
			
			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				fw.write("   " + reference + " = ");

				Assert.assertTrue(PidType.isPid(reference.getType())
						|| ChanType.isChan(reference.getType()));
				if (PidType.isPid(reference.getType())) {
					fw.write("applyToPr");
				} else {
					fw.write("applyToCh");
				}
				fw.write("(*alpha," + reference);
				if (ChanType.isChan(reference.getType())) {
					fw.write("-1)+1;\n");
				} else {
					fw.write(");\n");
				}

			}

			for (ListIterator iter = sensitivelyIndexedArrays.listIterator(); iter
					.hasNext();) {
				PidIndexedArrayReference reference = (PidIndexedArrayReference) iter
						.next();
				Assert.assertTrue(((ArrayType) reference.getType())
						.getIndexType() instanceof VisibleType);
				Assert.assertTrue(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
						.getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar swapper[" + reference.getArrayLength()
						+ "];\n");
				fw.write("       for(j=0; j<" + reference.getArrayLength()
						+ "; j++) {\n");
				fw.write("          swapper[applyToPr(*alpha,j)] = "
						+ reference + "[j];\n");
				fw.write("       }");
				fw.write("       memcpy(" + reference
						+ ",swapper," + reference.getArrayLength()
						+ "*sizeof(uchar));\n");
				fw.write("   }\n");

			}

			fw.write("\n");
		}
	}

	private void permuteChannelContents(FileWriter fw) throws IOException {

		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsSensitiveType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (PidType.isPid(flattenedFieldTypes.get(j))
							|| ChanType.isChan(flattenedFieldTypes.get(j))) {
						fw.write("      ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + " = ");
						if (PidType.isPid(flattenedFieldTypes.get(j))) {
							fw.write("applyToPr");
						} else {
							Assert.assertTrue(ChanType.isChan(flattenedFieldTypes
									.get(j)));
							fw.write("applyToCh");
						}
						fw.write("(*alpha,((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j);
						if (ChanType.isChan(flattenedFieldTypes.get(j))) {
							fw.write("-1)+1;\n");
						} else {
							Assert.assertTrue(PidType.isPid(flattenedFieldTypes
									.get(j)));
							fw.write(");\n");
						}
					}
				}
				fw.write("   }\n");
			}
		}
	}

	private void permuteProcesses(FileWriter fw) throws IOException {
		for (int j = 1; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			int proctypeIdentifier = typeInfo.proctypeId(proctypeName);
			fw.write("   j = applyToPr(*alpha," + j + ");\n");
			fw.write("   memcpy(SEG(&temp,j),SEG(s," + j + "),sizeof(P"
					+ proctypeIdentifier + "));\n");
			fw.write("   VAR(&temp,j,_pid,P" + proctypeIdentifier
					+ ")=VAR(s,j,_pid,P" + proctypeIdentifier + ");\n");
			fw.write("\n");
		}
	}

	private void permuteChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getNoStaticChannels(); j++) {
			int chantypeIdentifier = j + 1;
			fw.write("   j = applyToCh(*alpha," + j + ");\n");
			fw.write("   memcpy(QSEG(&temp,j),QSEG(s," + j + "),sizeof(Q"
					+ chantypeIdentifier + "));\n");
			fw.write("   QVAR(&temp,j,_t,Q" + chantypeIdentifier
					+ ")=QVAR(s,j,_t,Q" + chantypeIdentifier + ");\n");
			fw.write("\n");
		}
	}

	private boolean containsSensitiveType(List<VisibleType> flattenedFieldTypes) {
		for (int i = 0; i < flattenedFieldTypes.size(); i++) {
			if (ChanType.isChan(flattenedFieldTypes.get(i))
					|| PidType.isPid(flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	/* Methods to apply a permutation to a state via transpositions */

	private void writeApplyPermToStateTranspositions()
			throws IOException {
		permutationFile.write("void applyPermToState(" + stateType + " *s, ");
		permutationFile.write("perm_t *alpha) {\n");
		permutationFile.write("   int i;\n");
		permutationFile.write("   for(i=0; i<alpha->prLength; i=i+2) {\n");
		permutationFile.write("      applyPrSwapToState(s,alpha->pr[i],alpha->pr[i+1]);\n");
		permutationFile.write("   }\n\n");
		permutationFile.write("   for(i=0; i<alpha->chLength; i=i+2) {\n");
		permutationFile.write("      applyChSwapToState(s,alpha->ch[i],alpha->ch[i+1]);\n");
		permutationFile.write("   }\n\n");
		permutationFile.write("}\n\n");
	}

	private void writeApplyChSwapToState() throws IOException {
		permutationFile.write("void applyChSwapToState(" + stateType + " *s, int a, int b) {\n");
		permutationFile.write("   uchar tempCid;\n");
		permutationFile.write("   int slot;\n");
		if(Config.VECTORIZE_ID_SWAPPING) {
			swapVectorizer.writeChannelSwaps(permutationFile);
		} else {
			swapProctypeLocalChannelVariables(permutationFile);
			swapChannelReferencesInChannels(permutationFile);
		}
		swapChannels(permutationFile);
		permutationFile.write("}\n\n");
	}

	private void writeApplyPrSwapToState() throws IOException {
		permutationFile.write("void applyPrSwapToState(" + stateType + " *s, int a, int b) {\n");
		permutationFile.write("   uchar tempPid;\n");
		permutationFile.write("   int slot;\n");

		if(Config.VECTORIZE_ID_SWAPPING) {
			swapVectorizer.writeProcessSwaps(permutationFile, "a", "b");
		} else {
			swapGlobalPidVariables(permutationFile,"a","b");
			swapLocalPidVariables(permutationFile, "a", "b");
			swapPidReferencesInChannels(permutationFile, "a", "b");
		}
		swapProcesses(permutationFile);
		permutationFile.write("}\n\n");
	}

	private void swapGlobalPidVariables(FileWriter fw, String one, String two) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		String referencePrefix = "s->";

		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {

				if (!(Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS)) {
					for (SensitiveVariableReference reference : SensitiveVariableReference.getSensitiveVariableReferences(
							name, ((VarEntry) entry).getType(), referencePrefix, typeInfo)) {
						Assert.assertTrue(PidType.isPid(reference.getType()));
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
					Assert.assertTrue(((ArrayType) reference.getType())
							.getIndexType() instanceof VisibleType);
					Assert.assertTrue(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
							.getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar temp;\n");
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

	private void swapLocalPidVariables(FileWriter fw, String one, String two) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			String referencePrefix = "((P" + typeInfo.proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();
			List<SensitiveVariableReference> sensitivelyIndexedArrays = new ArrayList<SensitiveVariableReference>();

			for(Iterator<Entry<String,VisibleType>> iter = typeInfo.getProctypeEntryForProcess(j).variableTypePairIterator(); iter.hasNext();) {
				Entry<String,VisibleType> entry = iter.next();

				referencesToPermute.addAll(SensitiveVariableReference.getSensitiveVariableReferences(
						entry.getKey(), entry.getValue(), referencePrefix, typeInfo));
				sensitivelyIndexedArrays
						.addAll(PidIndexedArrayReference.getSensitivelyIndexedArrayReferences(
								entry.getKey(), entry.getValue(), referencePrefix, typeInfo));
				
			}

			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				Assert.assertTrue(PidType.isPid(reference.getType())
						|| ChanType.isChan(reference.getType()));
				if (PidType.isPid(reference.getType())) {
					fw.write("   if(" + reference + "==" + one + ") {\n");
					fw.write("   " + reference + " = " + two + ";\n");
					fw.write("   } else if(" + reference
							+ "==" + two + ") {\n");
					fw.write("   " + reference + " = " + one + ";\n");
					fw.write("   }\n");
				}
			}

			for (ListIterator iter = sensitivelyIndexedArrays.listIterator(); iter
					.hasNext();) {
				PidIndexedArrayReference reference = (PidIndexedArrayReference) iter
						.next();
				Assert.assertTrue(((ArrayType) reference.getType())
						.getIndexType() instanceof VisibleType);
				Assert.assertTrue(PidType.isPid((VisibleType) ((ArrayType) reference.getType())
						.getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar temp;\n");
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

	private void swapChannelReferencesInChannels(FileWriter fw) throws IOException {
		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (ChanType.containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (ChanType.isChan(flattenedFieldTypes.get(j))) {
						fw.write("      if(((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "==a+1) {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=b+1;\n");
						fw.write("      } else if(((Q" + (i + 1) + " *)QSEG(s,"
								+ i + "))->contents[slot].fld" + j
								+ "==b+1) {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=a+1;\n");
						fw.write("      }\n");
					}
				}
				fw.write("   }\n");
			}
		}

	}

	private void swapPidReferencesInChannels(FileWriter fw, String one, String two) throws IOException {

		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (PidType.containsPidType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (PidType.isPid(flattenedFieldTypes.get(j))) {
						fw.write("      if(((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "==" + one + ") {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=" + two + ";\n");
						fw
								.write("      } else if(((Q" + (i + 1)
										+ " *)QSEG(s," + i
										+ "))->contents[slot].fld" + j
										+ "==" + two + ") {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=" + one + ";\n");
						fw.write("      }\n");
					}
				}
				fw.write("   }\n");
			}
		}

	}

	private void swapProctypeLocalChannelVariables(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = typeInfo.getProcessEntries()
					.get(j).getProctypeName();
			String referencePrefix = "((P" + typeInfo.proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();

			for(Iterator<Entry<String,VisibleType>> iter = typeInfo.getProctypeEntryForProcess(j).variableTypePairIterator(); iter.hasNext();) {
				Entry<String,VisibleType> entry = iter.next();
				referencesToPermute.addAll(SensitiveVariableReference.getSensitiveVariableReferences(
						entry.getKey(), entry.getValue(), referencePrefix, typeInfo));
			}
			
			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				Assert.assertTrue(PidType.isPid(reference.getType())
						|| ChanType.isChan(reference.getType()));
				if (ChanType.isChan(reference.getType())) {
					fw
							.write("   if(" + reference
									+ "==a+1) {\n");
					fw.write("      " + reference + " = b+1;\n");
					fw.write("   } else if(" + reference
							+ "==b+1) {\n");
					fw.write("      " + reference + " = a+1;\n");
					fw.write("   }\n");
				}
			}

			fw.write("\n");

		}
	}

	private void writePreprocessorMacros(FileWriter out) throws IOException {
		
		if (!usingMarkers()) {
			out.write("#include \"group.h\"\n\n");
		}
		
		out
				.write("#define SEG(state,pid) (((uchar *)state)+proc_offset[pid])\n");
		out.write("#define QSEG(state,cid) (((uchar *)state)+q_offset[cid])\n");
		out
				.write("#define VAR(state,pid,var,type) ((type *)SEG(state,pid))->var\n");
		out
				.write("#define QVAR(state,cid,var,type) ((type *)QSEG(state,cid))->var\n\n");


	}


	private void replaceWithRepresentativeStore(List<String> lines, int counter) {
		/* "&now" is being stored, replace "&now" with "rep(&now)". */
		lines.set(counter, lines.get(counter).replace("&now", "rep(&now)")); // If
	}

	private boolean lineInvolvesHashStore(List<String> lines, int counter) {
		return (lines.get(counter).contains("&now") && lines.get(counter)
				.contains("store"));
	}

	private void dealWithSympanHeader() throws IOException {
		List<String> lines = readFile("sympan.h");
		FileWriter out = new FileWriter("sympan.h");

		// Look through lines of "sympan.h".

		for (int counter = 0; counter < lines.size(); counter++) {
			lines.set(counter, lines.get(counter).replace("pan.", "sympan."));
			writeln(out, lines.get(counter));
			if (lines.get(counter).contains("function prototypes")) {
				out
						.write("State *rep(State *orig_now); /* ADDED FOR SYMMETRY */\n");
			}
		}
		out.close();
	}

	private void dealWithSegmentFiles() throws IOException {
		if(Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Copying files for segmented strategy:");
			
			FileManager.copyTextFile(Config.COMMON + "segment.h", "segment.h");
		}
	}
	
	private void dealWithGroupFiles() throws IOException, InterruptedException {
		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Copying template files for computing with permutations:");
		
		if (!usingMarkers() && Config.USE_TRANSPOSITIONS) {
			FileManager.copyTextFile(Config.COMMON + "groupTranspositions.c", "group.c");
			// Copy group theory files into current directory
			FileManager.copyTextFile(Config.COMMON + "groupTranspositions.h", "group.h");
		} else if (!usingMarkers() && !Config.USE_TRANSPOSITIONS) {
			/* Copy group theory files into current directory */
			FileManager.copyTextFile(Config.COMMON + "groupBasic.c", "group.c");
			FileManager.copyTextFile(Config.COMMON + "groupBasic.h", "group.h");
		}

		if (!usingMarkers()) {

			List<String> lines = readFile("group.h");

			FileWriter out = new FileWriter("group.h");
			for (int counter = 0; counter < lines.size(); counter++) {
				// Set number of processes and channels
				lines.set(counter, lines.get(counter).replace("<NO_PROCS>",
						String.valueOf(typeInfo.getNoProcesses())));
				lines.set(counter, lines.get(counter)
						.replace(
								"<NO_CHANS>",
								String.valueOf(typeInfo.getStaticChannelNames()
										.size())));
				writeln(out, lines.get(counter));
			}
			out.close();

		}

	}

	private void generatePanFiles() throws IOException, InterruptedException {
		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Using SPIN to generate pan files");
		execute("spin", "-a", specification); // Generate pan files.

		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Generating sympan files from pan files:");

		char[] endings = { 'c', 'h', 'b', 't', 'm' };
		for (char ending : endings) { // Copy pan files into sympan files
			FileManager.copyTextFile("pan." + ending, "sympan." + ending);
		}
	}

	private void writeGlobalVariablesForPartitionConstruction(FileWriter fw)
			throws IOException {
		for (int i = 0; i < typeInfo.getProctypeNames().size(); i++) {
			if(!typeInfo.getProctypeNames().get(i).equals(ProctypeEntry.initProctypeName)) {
				
				List<Integer> processIdsOfThisProctype = new ArrayList<Integer>();
				for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
					ProcessEntry process = (ProcessEntry) typeInfo
							.getProcessEntries().get(j);
					if (process.getProctypeName().equals(
							typeInfo.getProctypeNames().get(i))) {
						processIdsOfThisProctype.add(j);
					}
				}
	
				fw.write("int no_P" + i + " = " + processIdsOfThisProctype.size()
						+ ";\n");
				fw.write("int P" + i + "_procs[" + processIdsOfThisProctype.size()
						+ "] = { ");
				for (int j = 0; j < processIdsOfThisProctype.size(); j++) {
					fw.write(processIdsOfThisProctype.get(j).toString());
					if (j < processIdsOfThisProctype.size() - 1) {
						fw.write(", ");
					}
				}
				fw.write(" };\n\n");
			}
		}

		int i = 0;
		for (Iterator iter = typeInfo.getDistinctChannelSignatures().iterator(); iter
				.hasNext(); i++) {
			ChannelEntry channelSignature = (ChannelEntry) iter.next();
			List<Integer> channelsOfThisSignature = new ArrayList<Integer>();
			for (int j = 0; j < typeInfo.getNoStaticChannels(); j++) {
				ChannelEntry channel = (ChannelEntry) typeInfo
						.getEnvEntry((String) typeInfo.getStaticChannelNames()
								.get(j));
				if (channel.equal(channelSignature)) {
					channelsOfThisSignature.add(new Integer(j));
				}
			}

			fw.write("int no_Chantype" + i + " = "
					+ channelsOfThisSignature.size() + ";\n");
			fw.write("int chantype" + i + "_chans["
					+ channelsOfThisSignature.size() + "] = { ");
			for (int j = 0; j < channelsOfThisSignature.size(); j++) {
				fw.write(channelsOfThisSignature.get(j).toString());
				if (j < channelsOfThisSignature.size() - 1) {
					fw.write(", ");
				}
			}
			fw.write(" };\n\n");
		}

	}

	private void writeConstructPartition(FileWriter fw) throws IOException {
		writeGlobalVariablesForPartitionConstruction(fw);

		fw.write("char* constructPartition(const State *s) {\n");
		fw.write("   int processClasses[NO_PROCS];\n");
		fw.write("   int channelClasses[NO_CHANS];\n");
		fw.write("   int noProcessClasses = 0;\n");
		fw.write("   int noChannelClasses = 0;\n\n");
		fw.write("   int i;\n");
		fw.write("   for(i=0; i<NO_PROCS; i++) {\n");
		fw.write("      processClasses[i] = -1;\n");
		fw.write("   }\n\n");
		fw.write("   for(i=0; i<NO_CHANS; i++) {\n");
		fw.write("      channelClasses[i] = -1;\n");
		fw.write("   }\n\n");
		fw
				.write("   char* result = (char*)malloc(3*(NO_PROCS+NO_CHANS*sizeof(char)));\n");
		fw.write("   result[0] = '\\0';\n\n");
		fw.write("   char temp[5];\n\n");
		fw.write("   strcat(result,\"ptn:\");\n\n");

		for (int i = 0; i < typeInfo.getProctypeNames().size(); i++) {
			if(!typeInfo.getProctypeNames().get(i).equals(ProctypeEntry.initProctypeName)) {
				fw.write("  for(i=0; i<no_P" + i + "; i++) {\n");
				fw.write("    if(processClasses[P" + i + "_procs[i]]==-1) {\n");
				fw.write("      sprintf(temp,\"%d\",P" + i + "_procs[i]);\n");
				fw.write("      strcat(result,\"|\");\n");
				fw.write("      strcat(result,temp);\n\n");
	
				fw.write("      processClasses[P" + i
						+ "_procs[i]]=++noProcessClasses;\n");
				fw.write("      int j;\n");
				fw.write("      for(j=i+1; j<no_P" + i + "; j++) {\n");
				fw.write("        if(equalProcesses(SEG(s,P" + i
						+ "_procs[i]),SEG(s,P" + i + "_procs[j]),P" + i + "_procs[i],P" + i + "_procs[j]," + i + ",s)) {\n");
				fw.write("          processClasses[P" + i
						+ "_procs[j]] = noProcessClasses;\n");
				fw.write("          strcat(result,\",\");\n");
				fw.write("          sprintf(temp,\"%d\",P" + i + "_procs[j]);\n");
				fw.write("          strcat(result,temp);\n");
				fw.write("        }\n");
				fw.write("      }\n");
				fw.write("    }\n");
				fw.write("  }\n\n");
			}
		}

		for (int i = 0; i < typeInfo.getDistinctChannelSignatures().size(); i++) {
			fw.write("  for(i=0; i<no_Chantype" + i + "; i++) {\n");
			fw.write("    if(channelClasses[chantype" + i
					+ "_chans[i]]==-1) {\n");
			fw.write("      sprintf(temp,\"%d\",chantype" + i
					+ "_chans[i]+NO_PROCS);\n");
			fw.write("      strcat(result,\"|\");\n");
			fw.write("      strcat(result,temp);\n\n");

			fw.write("      channelClasses[chantype" + i
					+ "_chans[i]]=++noChannelClasses;\n");
			fw.write("      int j;\n");

			fw.write("      for(j=i+1; j<no_Chantype" + i + "; j++) {\n");
			fw.write("        if(equalChannels(QSEG(s,chantype" + i
					+ "_chans[i]),QSEG(s,chantype" + i + "_chans[j]),chantype"
					+ i + "_chans[i] + 1" + ")) {\n");
			fw.write("          channelClasses[chantype" + i
					+ "_chans[j]] = noChannelClasses;\n");
			fw.write("          strcat(result,\",\");\n");
			fw.write("          sprintf(temp,\"%d\",chantype" + i
					+ "_chans[j]+NO_PROCS);\n");
			fw.write("          strcat(result,temp);\n");
			fw.write("        }\n");
			fw.write("      }\n");
			fw.write("    }\n");
			fw.write("  }\n\n");
		}
		fw.write("   strcat(result,\"\");\n\n");
		fw.write("   return result;\n");
		fw.write("}\n\n");
	}

	private void writeEqualChannels(FileWriter fw) throws IOException {

		fw.write("int equalChannels(void* q1, void* q2, int qt) {");
		fw.write("   int slot;\n\n");
		fw.write("   switch(qt) {\n");
		for (int i = 1; i <= typeInfo.getNoStaticChannels(); i++) {
			String q1Prefix = "((Q" + i + "*)q1)->";
			String q2Prefix = "((Q" + i + "*)q2)->";

			fw.write("      case " + i + ": if(" + q1Prefix + "Qlen!="
					+ q2Prefix + "Qlen) return 0;\n");

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i - 1))).getType();
			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsInsensitiveType(flattenedFieldTypes)) {

				fw.write("        for(slot=0; slot<((Q" + i
						+ "*)q1)->Qlen; slot++) {\n\n");

				for (int k = 0; k < flattenedFieldTypes.size(); k++) {
					if (!(ChanType.isChan(flattenedFieldTypes.get(k)) || PidType.isPid(flattenedFieldTypes
							.get(k)))) {
						fw.write("          if(" + q1Prefix
								+ "contents[slot].fld" + k + "!=" + q2Prefix
								+ "contents[slot].fld" + k + ") return 0;\n");
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
		fw.write("int equalProcesses(const void* p1, const void* p2, const int i, const int j, const int pt, const State* s) {\n\n");

		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if (entry instanceof VarEntry) {
				VisibleType entryType = ((VarEntry)entry).getType();
				if(entryType instanceof ArrayType && PidType.isPid((VisibleType) ((ArrayType)entryType).getIndexType()) &&
						(((ArrayType)entryType).getElementType() instanceof SimpleType)) {
					if(PidType.isPid(((ArrayType)entryType).getElementType())) {
						fw.write("   if((s->" + name + "[i]==0 && s->" + name + "[j]!=0)||(s->" + name + "[i]!=0 && s->" + name + "[j]==0)) return 0;\n");
					} else {
						fw.write("   if(s->" + name + "[i]!=s->" + name + "[j]) return 0;\n");
					}
				}
			}
		}
		
		fw.write("   switch(pt) {\n");
		for (int i = 0; i < typeInfo.getProctypeNames().size(); i++) {
			fw.write("      case " + i + ": return ((P" + i + "*)p1)->_p==((P"
					+ i + "*)p2)->_p");

			List<String> referencesToCompare = new ArrayList<String>();

			ProctypeEntry proctype = (ProctypeEntry) typeInfo
					.getEnvEntry((String) typeInfo.getProctypeNames().get(i));

			Map<String, EnvEntry> localScope = proctype.getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter
					.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {
					referencesToCompare
							.addAll(SensitiveVariableReference.getInsensitiveVariableReferences(varName,
									((VarEntry) localScope.get(varName))
											.getType(), "", typeInfo));
				}
			}

			for (ListIterator iter = referencesToCompare.listIterator(); iter
					.hasNext();) {
				String reference = (String) iter.next();
				fw.write(" && ((P" + i + "*)p1)->" + reference + "==((P" + i
						+ "*)p2)->" + reference);
			}

			fw.write(";\n");

		}

		fw.write("  }\n\n");
		fw.write("  printf(\"Error in process comparison\\n\");\n\n");
		fw.write("  return 0;\n\n");
		fw.write("}\n\n");

	}

	private void writeLt(FileWriter fw) throws IOException {
		if(Config.VECTORIZE_ID_SWAPPING) {
			fw.write("int lt(const AugmentedState *s, const AugmentedState *t) {\n");
			fw.write("   return memcmp(&(s->state), &(t->state),vsize)<0;\n");
			fw.write("}\n\n");
			return;
		}
		
		fw.write("int lt(State *s, State *t) {\n");
		fw.write("  int slot;\n\n");

		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if (entry instanceof VarEntry) {
				VisibleType entryType = ((VarEntry)entry).getType();
				if(entryType instanceof ArrayType && PidType.isPid((VisibleType) ((ArrayType)entryType).getIndexType()) &&
						(((ArrayType)entryType).getElementType() instanceof SimpleType)) {
					for(int i=1; i<typeInfo.getNoProcesses(); i++) {
					
						if(PidType.isPid(((ArrayType)entryType).getElementType())) {
							fw.write("   if(s->" + name + "[" + i + "]==0 && t->" + name + "[" + i + "]!=0) return 1;\n");
							fw.write("   if(s->" + name + "[" + i + "]!=0 && t->" + name + "[" + i + "]==0) return 0;\n");
						} else {
							fw.write("   if(s->" + name + "[" + i + "]<t->" + name + "[" + i + "]) return 1;\n");
							fw.write("   if(s->" + name + "[" + i + "]>t->" + name + "[" + i + "]) return 0;\n");
						}
					}
				}
			}
		}
		
		int j = 0;
		
		for (ProcessEntry entry : typeInfo.getProcessEntries()) {
			String proctypeName = entry.getProctypeName();
			if(!proctypeName.equals(ProctypeEntry.initProctypeName)) {
				String sPrefix = "((P" + typeInfo.proctypeId(proctypeName) + " *)SEG(s," + j
						+ "))->";
				String tPrefix = "((P" + typeInfo.proctypeId(proctypeName) + " *)SEG(t," + j
						+ "))->";
				ProctypeEntry proctype = (ProctypeEntry) typeInfo
						.getEnvEntry(proctypeName);
		
				fw.write("  if(" + sPrefix + "_p < " + tPrefix + "_p) return 1;\n");
				fw.write("  if(" + sPrefix + "_p > " + tPrefix
						+ "_p) return 0;\n\n");
		
				List<String> referencesToCompare = new ArrayList<String>();
		
				Map<String, EnvEntry> localScope = proctype.getLocalScope();
				for (String varName : localScope.keySet()) {
					if (localScope.get(varName) instanceof VarEntry) {
						referencesToCompare
								.addAll(SensitiveVariableReference.getInsensitiveVariableReferences(varName,
										((VarEntry) localScope.get(varName))
												.getType(), "", typeInfo));
					}
				}
		
				for (String reference : referencesToCompare) {
					fw.write("  if(" + sPrefix + reference + " < " + tPrefix
							+ reference + ") return 1;\n");
					fw.write("  if(" + sPrefix + reference + " > " + tPrefix
							+ reference + ") return 0;\n\n");
				}
			}
			j++;
		}

		for (j = 0; j < typeInfo.getNoStaticChannels(); j++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							j))).getType();
			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			String sPrefix = "((Q" + (j + 1) + " *)QSEG(s," + j + "))->";
			String tPrefix = "((Q" + (j + 1) + " *)QSEG(t," + j + "))->";

			fw.write("  if(" + sPrefix + "Qlen < " + tPrefix
					+ "Qlen) return 1;\n");
			fw.write("  if(" + sPrefix + "Qlen > " + tPrefix
					+ "Qlen) return 0;\n\n");

			if (containsInsensitiveType(flattenedFieldTypes)) {

				fw.write("  for(slot=0; slot<((Q" + (j + 1) + " *)QSEG(s," + j
						+ "))->Qlen; slot++) {\n\n");

				for (int k = 0; k < flattenedFieldTypes.size(); k++) {
					if (!(ChanType.isChan(flattenedFieldTypes.get(k)) || PidType.isPid(flattenedFieldTypes
							.get(k)))) {
						fw.write("    if(" + sPrefix + "contents[slot].fld" + k
								+ " < " + tPrefix + "contents[slot].fld" + k
								+ ") return 1;\n");
						fw.write("    if(" + sPrefix + "contents[slot].fld" + k
								+ " > " + tPrefix + "contents[slot].fld" + k
								+ ") return 0;\n\n");
					}
				}

				fw.write("   }\n\n");
			}
		}
		fw.write("   return 0;\n");
		fw.write("}\n\n");
	}

	private boolean containsInsensitiveType(List<VisibleType> flattenedFieldTypes) {
		for (int i = 0; i < flattenedFieldTypes.size(); i++) {
			if (!(PidType.isPid(flattenedFieldTypes.get(i)) || ChanType.isChan(flattenedFieldTypes
					.get(i)))) {
				return true;
			}
		}
		return false;
	}

	private void swapProcesses(FileWriter fw) throws IOException {
		for (int j = 1; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			int proctypeIdentifier = typeInfo.proctypeId(proctypeName);
			fw.write("   if(a==" + j + ") {\n");
			swapTwoProcesses(fw, proctypeIdentifier, "a", "b");

			if(Config.VECTORIZE_ID_SWAPPING) {
				swapVectorizer.swapTwoProcesses(fw, j, "a", "b");
			}

			fw.write("      return;\n");
			fw.write("   }\n\n");
		}
		
	}

	private void swapTwoProcesses(FileWriter fw, int proctypeIdentifier, String one, String two) throws IOException {
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

	private void swapChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getNoStaticChannels(); j++) {
			int chantypeIdentifier = j + 1;
			fw.write("   if(a==" + j + ") {\n");
			fw.write("      Q" + chantypeIdentifier + " temp;\n");
			fw.write("      memcpy(&temp,QSEG(s,a),sizeof(Q"
					+ chantypeIdentifier + "));\n");
			fw.write("      memcpy(QSEG(s,a),QSEG(s,b),sizeof(Q"
					+ chantypeIdentifier + "));\n");
			fw.write("      memcpy(QSEG(s,b),&temp,sizeof(Q"
					+ chantypeIdentifier + "));\n");
			fw.write("      tempCid = QVAR(s,a,_t,Q" + chantypeIdentifier
					+ ");\n");
			fw.write("      QVAR(s,a,_t,Q" + chantypeIdentifier
					+ ") = QVAR(s,b,_t,Q" + chantypeIdentifier + ");\n");
			fw.write("      QVAR(s,b,_t,Q" + chantypeIdentifier
					+ ") = tempCid;\n");

			if(Config.VECTORIZE_ID_SWAPPING) {
				swapVectorizer.swapTwoChannels(fw, j, "a", "b");
			}
			
			fw.write("      return;\n");
			fw.write("   };\n");
			fw.write("\n");
		}
	}

	private static void writeln(FileWriter fw, String s) throws IOException {
		fw.write(s + "\n");
	}

	private static String convertPerm(String alpha) {
		// Convert a GAP permutation into a permutation for SPIN
		return alpha.replace(',', ' ');
	}

	public static String compare(String x, String y) {
		if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
			return "lt(" + x + "," + y + ")";
		}
		return memoryCompare + "(" + x + "," + y + ",vsize)<0";
	}

	private static boolean usingMarkers() {
		return Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS
				|| Config.REDUCTION_STRATEGY == Strategy.EXACTMARKERS;
	}

	private static List<String> readFile(String fname) throws IOException {
		List<String> result = new ArrayList<String>();
		try {
			BufferedReader in = new BufferedReader(new FileReader(fname));
			String line;
			while ((line = in.readLine()) != null) {
				result.add(line);
			}
		} catch (IOException e) {
			System.out.println("Error reading from file \"" + fname + "\".");
			throw e;
		}
		return result;
	}

	private static void execute(String command, String option, String argument)
			throws IOException, InterruptedException {

		try {
			Process p = Runtime.getRuntime().exec(
					command + " " + option + " " + argument);
			p.waitFor();
		} catch (IOException e) {
			System.out.println("Error executing command \"" + command + " "
					+ option + " " + argument + "\".");
			e.printStackTrace();
			throw e;
		} catch (InterruptedException e) {
			System.out.println("Error executing command \"" + command + " "
					+ option + " " + argument + "\".");
			throw e;
		}
	}


}
