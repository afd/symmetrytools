package src.symmreducer;

import java.io.BufferedReader;
import java.io.BufferedWriter;
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
import src.etch.env.TypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.SimpleType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.ProgressPrinter;
import src.utilities.Strategy;
import src.utilities.StringHelper;

public class SymmetryApplier {

	protected StaticChannelDiagramExtractor typeInfo;

	private String specification;

	private String groupGenerators;
	
	public SymmetryApplier(String specification,
			StaticChannelDiagramExtractor typeInfo, String groupGenerators) {
		this.specification = specification;
		this.typeInfo = typeInfo;
		this.groupGenerators = groupGenerators;
	}

	public void applySymmetry() {
		try {
			generatePanFiles();
			dealWithSympanHeader();
			dealWithSympanBody();
			dealWithGroupFiles();
			dealWithSegmentFiles();
			dealWithSymmetryThreadFiles();
		} catch (Exception e) {
			System.out
					.println("An error occurred while constructing the \"sympan\" files.");
			e.printStackTrace();
			System.exit(1);
		}
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

				if (Config.USE_TRANSPOSITIONS) {
					writeApplyPrSwapToState(out);
					if (!usingMarkers()) {
						writeApplyChSwapToState(out);
						writeApplyPermToStateTranspositions(out);
					}
				} else if (!usingMarkers()) {
					writeApplyPermToStateBasic(out);
				}

				if(Config.PTHREADS) {
					out.write("\n#include \"symmetry_threads.h\"\n\n");
					out.write("pthread_mutex_t min_mutex = PTHREAD_MUTEX_INITIALIZER;\n\n");
				}
				
				if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
					writeLt(out);
					writeEqualProcesses(out);
					writeEqualChannels(out);
					writeConstructPartition(out);
					out.write("#include \"segment.h\"\n");

				} else if (Config.REDUCTION_STRATEGY == Strategy.FLATTEN) {
					writeFlatten(out);
				} else if (usingMarkers()) {
					writeMarkers(out);
					if (Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS) {
						writeMarkPID(out);
					}
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
				
				/*if(Config.PTHREADS) {
					out.write("   join_threads();\n\n");
				}*/
			}

			if (!usingMarkers() && mainMethodReached(lines, counter)) {
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

				for (int groupInfoCounter = 0; groupInfoCounter < groupInfo
						.size(); groupInfoCounter++) {
					// Sims method
					if (Config.USE_STABILISER_CHAIN
							&& groupInfo.get(groupInfoCounter).contains(
									"<enumerate>")) {
						groupInfoCounter = writeInstantiateStabiliserChain(
								groupInfo, out, setCounter, groupInfoCounter);
					} else {
						if (groupInfo.get(groupInfoCounter).contains("<")) {
							// skip the line which says how many
							// permutations there will be
							groupInfoCounter++;
							setCounter++;
							index = 0;
						} else {
							groupInfoCounter = writeInstantiateElement(
									groupInfo, out, setCounter, index++,
									groupInfoCounter);
						}
					}
				}
				
				if(Config.PTHREADS) {
					out.write("   start_threads();\n\n");
				}
			}
		}
		out.close();
	}

	private int writeInstantiateElement(List<String> groupInfo, FileWriter out,
			int setCounter, int index, int groupInfoCounter) throws IOException {
		out.write("   elementset_" + setCounter + "[" + index
				+ "]=constructPerm(\"");
		String perm = groupInfo.get(groupInfoCounter);
		while (perm.contains("\\")) {
			perm = perm.substring(0, perm.length() - 2)
					+ groupInfo.get(++groupInfoCounter);
		}
		if (Config.USE_TRANSPOSITIONS) {
			out.write(StringHelper.trimWhitespace(perm));
		} else {
			out.write(convertPerm(StringHelper.trimWhitespace(perm)));
		}
		out.write("\");\n");
		return groupInfoCounter;
	}

	private int writeInstantiateStabiliserChain(List<String> groupInfo,
			FileWriter out, int setCounter, int groupInfoCounter)
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
			out.write("\n   elementset_" + setCounter + "[" + partitionCounter
					+ "] = malloc(" + partitionSize
					+ " * sizeof(perm_t));\n");
			if (Config.USE_TRANSPOSITIONS) {
				out.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][0] = constructPerm(\"\");\n");
			} else {
				out.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][0] = constructPerm(\"()\");\n");
			}
			for (int cosetrepCounter = 1; cosetrepCounter < partitionSize; cosetrepCounter++) {
				out.write("   elementset_" + setCounter + "["
						+ partitionCounter + "][" + cosetrepCounter
						+ "] = constructPerm(\"");
				String perm = groupInfo.get(groupInfoCounter);
				while (perm.contains("\\")) {
					perm = perm.substring(0, perm.length() - 2)
							+ groupInfo.get(++groupInfoCounter);
				}
				if (Config.USE_TRANSPOSITIONS) {
					out.write(StringHelper.trimWhitespace(perm));
				} else {
					out.write(convertPerm(StringHelper.trimWhitespace(perm)));
				}
				out.write("\");\n");
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
					out.write("perm_t* elementset_");
				} else {
					out.write("perm_t elementset_");
				}
				out.write(setcounter
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

	private void writeRepFunction(List<String> groupInfo, FileWriter out)
			throws IOException {

		if(Config.PTHREADS && (Config.REDUCTION_STRATEGY==Strategy.ENUMERATE)) {
			writeRepPthreadsEnumerate(groupInfo, out);
			return;
		}
		
		out.write("\nState *rep(State *orig_now) {\n\n");

		if (usingMarkers()) {
			int procsminus1 = typeInfo.getNoProcesses() - 1;
			// FOR SIMPLICITY, I HAVE INCLUDED DUPLICATE CODE FOR
			// EACH MARKERS STRATEGY.
			if (Config.REDUCTION_STRATEGY == Strategy.EXACTMARKERS) {
				writeRepExactMarkers(out, procsminus1);
			} else if (Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS) {
				writeRepApproxMarkers(out, procsminus1);
			}
		} else {
			out.write("   memcpy(&min_now,orig_now, vsize);\n");
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
					writeRepEnumerateBasic(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}

				// MINIMISING SET STRATEGY
				if (groupInfo.get(groupInfoCounter).contains("<minimise>")) {
					writeRepMinimisingSet(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}

				// LOCAL SEARCH STRATEGY

				if (groupInfo.get(groupInfoCounter).contains("<localsearch>")) {
					writeRepLocalSearch(groupInfo, out, groupInfoCounter,
							setCounter);
					setCounter++;
				}

				groupInfoCounter++;
			}

			if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
				out.write("   segment(&min_now);\n\n");
			}

		}
		out.write("   return &min_now;\n");
		out.write("}\n\n");
	}

	private void writeRepPthreadsEnumerate(List<String> groupInfo, FileWriter out) throws IOException {
		Assert.assertTrue(Config.REDUCTION_STRATEGY==Strategy.ENUMERATE);

		out.write("State* original;\n\n");

		out.write("void * thread_body(void* arg) {\n");
		out.write("   int id, start, end, i;\n");
		
		if(Config.USE_STABILISER_CHAIN) {
			writeThreadBodyStabiliserChain(out, groupInfo);
		} else {
			writeThreadBodyBasic(out, Integer.parseInt(StringHelper.trimWhitespace(groupInfo.get(1))));
		}

		out.write("   return 0;\n\n");
		out.write("}\n\n\n");


		out.write("State *rep(State *orig_now) {\n");
		out.write("   memcpy(&min_now,orig_now, vsize);\n");
		out.write("   original = orig_now;\n");
		out.write("   wake_threads();\n");
		out.write("   wait_for_threads();\n");
		out.write("   return &min_now;\n");
		out.write("}\n\n");
				
	}

	private void writeThreadBodyBasic(FileWriter out, final int numberOfNonTrivialGroupElements) throws IOException {
		out.write("   id = *(int*)arg;\n");
		out.write("   get_data_section(&start, &end, id, " + numberOfNonTrivialGroupElements + ");\n\n");

		out.write("   while(working(id)) {\n");
		out.write("      State partial_min;\n");
		out.write("      State temp;\n");
		out.write("      memcpy(&partial_min, original, vsize);\n\n");

		out.write("      for(i=start; i<end; i++) {\n");
		out.write("         memcpy(&temp, original, vsize);\n");
		out.write("         applyPermToState(&temp, &(elementset_1[i]));\n");
		out.write("         if(memcmp(&temp,&partial_min,vsize)<0) {\n");
		out.write("            memcpy(&partial_min,&temp,vsize);\n");
		out.write("         }\n");
		out.write("      }\n\n");

		out.write("      pthread_mutex_lock(&min_mutex);\n");
		out.write("      if(memcmp(&partial_min, &min_now, vsize)<0) {\n");
		out.write("         memcpy(&min_now, &partial_min, vsize);\n");
		out.write("      }\n");
		out.write("      pthread_mutex_unlock(&min_mutex);\n");
		out.write("      sleep(id);\n");
		out.write("   }\n\n");

	}

	private void writeThreadBodyStabiliserChain(FileWriter out, List<String> groupInfo) throws IOException {

		final int stabiliserChainSize = getSizeOfStabiliserChain(groupInfo, 0);

		List<Integer> stabiliserChainComponentSizes = getStabiliserChainComponentSizes(groupInfo, 0, stabiliserChainSize);

		int numberOfGroupElements = getSizeOfGroupFromStabiliserChainComponentSizes(stabiliserChainComponentSizes);

		out.write("   int ");
		for(int i=0; i<stabiliserChainSize; i++) {
			out.write("start_" + i + ", ");
		}
		out.write("count;\n");
		
		out.write("   id = *(int*)arg;\n");
		out.write("   get_data_section(&start, &end, id, " + numberOfGroupElements + ");\n\n");
		
		out.write("   while(working(id)) {\n");
		out.write("      State partial_min;\n");
		out.write("      memcpy(&partial_min, original, vsize);\n\n");

		int divisor = 1;
		for(int i=0; i<stabiliserChainSize; i++) {
			out.write("   start_" + i + " = (start/" + divisor + ")%" + stabiliserChainComponentSizes.get(i) + ";\n"); 
			divisor *= stabiliserChainComponentSizes.get(i);
		}
		out.write("   count = 0;\n");
		
		List<String> start = new ArrayList<String>();
		List<String> end = new ArrayList<String>();

		for(int i=0; i<stabiliserChainSize ; i++) {
			start.add("start_" + i + ", start_" + i + "=0");
			end.add(stabiliserChainComponentSizes.get(i).toString());
		}

		outputSimsEnumeration(out, 1, stabiliserChainSize, start, end, "partial_min", "original");

		out.write("      pthread_mutex_lock(&min_mutex);\n");
		out.write("      if(memcmp(&partial_min, &min_now, vsize)<0) {\n");
		out.write("         memcpy(&min_now, &partial_min, vsize);\n");
		out.write("      }\n");
		out.write("      pthread_mutex_unlock(&min_mutex);\n");
		out.write("      sleep(id);\n");
		out.write("   }\n\n");
	}

	private int getSizeOfGroupFromStabiliserChainComponentSizes(List<Integer> stabiliserChainComponentSizes) {
		int numberOfNonTrivialGroupElements;
		numberOfNonTrivialGroupElements = stabiliserChainComponentSizes.get(0);
		for(int i=1; i<stabiliserChainComponentSizes.size(); i++) {
			numberOfNonTrivialGroupElements *= stabiliserChainComponentSizes.get(i);
		}
		return numberOfNonTrivialGroupElements;
	}

	private void writeRepLocalSearch(List<String> groupInfo, FileWriter out,
			int groupInfoCounter, int setCounter) throws IOException {
		int setSize = Integer.parseInt(StringHelper.trimWhitespace(groupInfo
				.get(groupInfoCounter + 1)));
		out.write("   {\n");
		out.write("      int j;\n");
		out.write("      State current_min, tmp_now;\n");
		out.write("      do {\n");
		out.write("         memcpy(&current_min,&min_now,vsize);\n\n");
		out.write("         for(j=0; j<" + setSize + "; j++) {\n");
		out.write("            memcpy(&tmp_now,&current_min,vsize);\n");
		out.write("            applyPermToState(&tmp_now,&(elementset_"
				+ setCounter + "[j]));\n");
		// this could probably be made more efficient
		out.write("            if(" + compare("&tmp_now", "&min_now") + ") {\n");
		out.write("               memcpy(&min_now,&tmp_now,vsize);\n");
		out.write("            }\n");
		out.write("         }\n");
		out.write("      } while(memcmp(&min_now,&current_min,vsize)!=0);\n\n");
		out.write("   }\n");
	}

	private void writeRepMinimisingSet(List<String> groupInfo, FileWriter out,
			int groupInfoCounter, int setCounter) throws IOException {
		int setSize = Integer.parseInt(StringHelper.trimWhitespace(groupInfo
				.get(groupInfoCounter + 1)));
		out.write("   {\n");
		out.write("      int j;\n");
		out.write("      State current_min, tmp_now;\n");
		out.write("      do {\n");
		out.write("         memcpy(&current_min,&min_now,vsize);\n\n");
		out.write("         for(j=0; j<" + setSize + "; j++) {\n");
		out.write("            memcpy(&tmp_now,&min_now,vsize);\n");
		out.write("            applyPermToState(&tmp_now,&(elementset_"
				+ setCounter + "[j]));\n");
		// this could probably be made more efficient
		out.write("            if(" + compare("&tmp_now", "&min_now") + ") {\n");
		out.write("               memcpy(&min_now,&tmp_now,vsize);\n");
		out.write("            }\n");
		out.write("         }\n");
		out.write("      } while(memcmp(&min_now,&current_min,vsize)!=0);\n\n");
		out.write("   }\n");
	}

	private void writeRepEnumerateBasic(List<String> groupInfo, FileWriter out,
			int groupInfoCounter, int setCounter) throws IOException {
		int setSize = Integer.parseInt(StringHelper.trimWhitespace(groupInfo
				.get(groupInfoCounter + 1)));
		out.write("   {\n");
		out.write("      int j;\n");
		out.write("      State tmp_now, current_min;\n");

		out.write("      memcpy(&tmp_now, &min_now, vsize);\n");
		out.write("      memcpy(&current_min, &min_now, vsize);\n");
		out.write("      for(j=0; j<" + setSize + "; j++) {\n");
		out.write("         applyPermToState(&tmp_now,&(elementset_"
				+ setCounter + "[j]));\n");
		out.write("         if(" + compare("&tmp_now", "&current_min")
				+ ") {\n");
		out.write("            memcpy(&current_min,&tmp_now,vsize);\n");
		out.write("         }\n");
		out.write("         memcpy(&tmp_now,&min_now,vsize);\n");
		out.write("      }\n");
		out.write("      memcpy(&min_now,&current_min,vsize);\n\n");
		out.write("   }\n");
	}


	private int writeRepEnumerateStabiliserChain(List<String> groupInfo,
			FileWriter out, int groupInfoCounter, int setCounter)
			throws IOException {
		final int stabiliserChainSize = getSizeOfStabiliserChain(groupInfo, groupInfoCounter);
		List<Integer> stabiliserChainComponentSizes = getStabiliserChainComponentSizes(groupInfo, groupInfoCounter, stabiliserChainSize);
		System.out.println(stabiliserChainComponentSizes);
		
		List<String> start = new ArrayList<String>();
		List<String> end = new ArrayList<String>();

		
		for(int i=0; i<stabiliserChainSize; i++) {
			start.add("0");
			end.add(stabiliserChainComponentSizes.get(i).toString());
		}
		
		out.write("   {\n");

		out.write("   State originalForThisStrategy;\n");
		out.write("   memcpy(&originalForThisStrategy,&min_now,vsize);\n\n");

		outputSimsEnumeration(out, setCounter, stabiliserChainSize, start, end, "min_now", "&originalForThisStrategy");

		out.write("   } /* End of sims enumeration */\n");

		return newValueOfGroupInfoCounter(groupInfoCounter, groupInfo, stabiliserChainSize);

	}

	private void outputSimsEnumeration(FileWriter out, int setCounter, final int stabiliserChainSize, List<String> start, List<String> end, String minName, String originalName) throws IOException {
		System.out.println("Stabiliser chain size is " + stabiliserChainSize);
		
		out.write("   int ");
		for (int counter = 0; counter < stabiliserChainSize; counter++) {
			out.write("i" + counter);
			if (counter < (stabiliserChainSize - 1)) {
				out.write(", ");
			} else {
				out.write(";\n\n");
			}
		}
		out.write("   State partialImages[" + stabiliserChainSize + "];\n\n");
		for (int counter = 0; counter < stabiliserChainSize; counter++) {
			for (int whiteSpaceCounter = 0; whiteSpaceCounter < counter + 1; whiteSpaceCounter++) {
				out.write("   ");
			}
			int partitionIndex = stabiliserChainSize - counter - 1;
			out.write("for(i" + partitionIndex + "=" + start.get(partitionIndex) + "; ");
			
			
			out.write("(i" + partitionIndex + "<"
					+ end.get(partitionIndex) + ")");
			
			if(Config.PTHREADS) {
				out.write(" && (count<(end-start))");			
			}
			
			out.write("; i" + partitionIndex
					+ "++) {\n");

			indent(out, counter+2);

			if (counter == 0) {
				out.write("memcpy(&partialImages[" + partitionIndex
						+ "]," + originalName + ",vsize);\n");
			} else {
				out.write("memcpy(&partialImages[" + partitionIndex
						+ "],&partialImages[" + (partitionIndex + 1)
						+ "],vsize);\n");
			}
			for (int whiteSpaceCounter = 0; whiteSpaceCounter < counter + 2; whiteSpaceCounter++) {
				out.write("   ");
			}
			out.write("applyPermToState(&partialImages[" + partitionIndex
					+ "],&elementset_" + setCounter + "[" + partitionIndex
					+ "][i" + partitionIndex + "]);\n\n");
		}

		if(Config.PTHREADS) {
			indent(out, stabiliserChainSize+1);
			out.write("count++;\n");
		}
		
		indent(out,stabiliserChainSize+1);
		out	.write("if(" + compare("&partialImages[0]", "&" + minName) + ") {\n");

		indent(out, stabiliserChainSize+2);
		out.write("memcpy(&" + minName + ",&partialImages[0],vsize);\n");

		indent(out,stabiliserChainSize+1);
		out.write("}\n");

		for (int i = stabiliserChainSize; i > 0; i--) {
			indent(out, i);
			out.write("}\n");
		}
	}

	private List<Integer> getStabiliserChainComponentSizes(List<String> groupInfo, int groupInfoCounter, int stabChainSize) {
		List<Integer> partitionSize = new ArrayList<Integer>();

		int partitionCounter = 0;
		while(partitionCounter < stabChainSize) {
			if (groupInfo.get(groupInfoCounter).contains("coset")) {
				String[] cosetInfo = groupInfo.get(groupInfoCounter).split(":");
				partitionSize.add(Integer.parseInt(StringHelper
						.trimWhitespace(cosetInfo[1])));
				partitionCounter++;
			}
			groupInfoCounter++;
		}
		return partitionSize;
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
	
	
	private int getSizeOfStabiliserChain(List<String> groupInfo, int groupInfoCounter) {
		int stabChainSize = Integer.parseInt(StringHelper
				.trimWhitespace(groupInfo.get(groupInfoCounter + 1)));
		return stabChainSize;
	}

	private void indent(FileWriter out, int numberOfTabs) throws IOException {
		for (int counter = 0; counter < numberOfTabs; counter++) {
			out.write("   ");
		}
	}

	private void writeRepApproxMarkers(FileWriter out, final int procsminus1)
			throws IOException {
		out.write("   Marker markers[" + procsminus1 + "], orig_markers["
				+ procsminus1 + "], temp;\n");
		out.write("   State tempstate;\n");
		out.write("   int i, j, map[" + procsminus1 + "];\n\n");
		out.write("   memcpy(&min_now,orig_now,vsize);\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      mark(&markers[i],orig_now,i+1);\n");
		out.write("   }\n\n");
		out.write("   memcpy(orig_markers,markers," + procsminus1
				+ "*sizeof(Marker));\n\n");
		out.write("   for(i=0; i<" + (procsminus1 - 1) + "; i++) {\n");
		out.write("      for(j=i+1; j<" + procsminus1 + "; j++) {\n");
		out.write("         if(lt(markers,i,j,orig_now)) {\n");
		out.write("            memcpy(&temp,&markers[i],sizeof(Marker));\n");
		out.write("            memcpy(&markers[i],&markers[j],sizeof(Marker));\n");
		out.write("            memcpy(&markers[j],&temp,sizeof(Marker));\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      for(j=" + (procsminus1 - 1) + "; j>=0; j--) {\n");
		out.write("         if(eq(&markers[j],&orig_markers[i])) {\n");
					/* Check the next one....find the smallest */
		out.write("            map[i] = j;\n");
		out.write("            break;\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n\n");
		out.write("   markPIDs(&min_now,map);\n");
	}

	private void writeRepExactMarkers(FileWriter out, int procsminus1)
			throws IOException {
		out.write("   Marker markers[" + procsminus1 + "], temp;\n");
		out.write("   int i, j;\n");
		out.write("   memcpy(&min_now,orig_now,vsize);\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      mark(&markers[i],orig_now,i+1);\n");
		out.write("   }\n");
		out.write("   for(i=0; i<" + (procsminus1 - 1) + "; i++) {\n");
		out.write("      for(j=i+1; j<" + procsminus1 + "; j++) {\n");
		out.write("         if(lt(markers,i,j,orig_now)) {\n");
		out.write("            memcpy(&temp,&markers[i],sizeof(Marker));");
		out.write("            memcpy(&markers[i],&markers[j],sizeof(Marker));\n");
		out.write("            memcpy(&markers[j],&temp,sizeof(Marker));\n");
		out.write("            applyPrSwapToState(&min_now,i+1,j+1);\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n");
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
		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
				.getTopEntries();

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List<SensitiveVariableReference> sensitiveReferences = getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), "");
				for (SensitiveVariableReference reference : sensitiveReferences) {
					fw.write("   temp." + reference.getReference() + " = ");
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("applyToPr(*alpha,s->" + reference.getReference()
							+ ");\n");
				}

				List<PidIndexedArrayReference> sensitivelyIndexedArrays = getSensitivelyIndexedArrayReferences(
						name, ((VarEntry) entry).getType(), "");
				for (PidIndexedArrayReference reference : sensitivelyIndexedArrays) {
					Assert.assertTrue(((ArrayType) reference.getType()).getIndexType() instanceof VisibleType);
					Assert.assertTrue(isPid((VisibleType) ((ArrayType) reference.getType())
							.getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar swapper["
							+ reference.getArrayLength() + "];\n");
					fw.write("       for(j=0; j<" + reference.getArrayLength()
							+ "; j++) {\n");
					fw.write("          temp." + reference.getReference()
							+ "[applyToPr(*alpha,j)] = s->"
							+ reference.getReference() + "[j];\n");
					fw.write("       }");
					fw.write("   }\n");
				}
			}
		}
	}

	private void permuteProctypeLocalVariables(FileWriter fw)
			throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			String referencePrefix = "((P" + proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo
					.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();
			List<SensitiveVariableReference> sensitivelyIndexedArrays = new ArrayList<SensitiveVariableReference>();

			Map<String, EnvEntry> localScope = proctype.getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter
					.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {
					referencesToPermute.addAll(getSensitiveVariableReferences(
							varName, ((VarEntry) localScope.get(varName))
									.getType(), referencePrefix));
					sensitivelyIndexedArrays
							.addAll(getSensitivelyIndexedArrayReferences(
									varName, ((VarEntry) localScope
											.get(varName)).getType(),
									referencePrefix));
				}
			}

			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				fw.write("   " + reference.getReference() + " = ");

				Assert.assertTrue(isPid(reference.getType())
						|| isChan(reference.getType()));
				if (isPid(reference.getType())) {
					fw.write("applyToPr");
				} else {
					fw.write("applyToCh");
				}
				fw.write("(*alpha," + reference.getReference());
				if (isChan(reference.getType())) {
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
				Assert.assertTrue(isPid((VisibleType) ((ArrayType) reference.getType())
						.getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar swapper[" + reference.getArrayLength()
						+ "];\n");
				fw.write("       for(j=0; j<" + reference.getArrayLength()
						+ "; j++) {\n");
				fw.write("          swapper[applyToPr(*alpha,j)] = "
						+ reference.getReference() + "[j];\n");
				fw.write("       }");
				fw.write("       memcpy(" + reference.getReference()
						+ ",swapper," + reference.getArrayLength()
						+ "*sizeof(uchar));\n");
				fw.write("   }\n");

			}

			fw.write("\n");
		}
	}

	private void permuteChannelContents(FileWriter fw) throws IOException {

		for (int i = 0; i < typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsSensitiveType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (isPid(flattenedFieldTypes.get(j))
							|| isChan(flattenedFieldTypes.get(j))) {
						fw.write("      ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + " = ");
						if (isPid(flattenedFieldTypes.get(j))) {
							fw.write("applyToPr");
						} else {
							Assert.assertTrue(isChan(flattenedFieldTypes
									.get(j)));
							fw.write("applyToCh");
						}
						fw.write("(*alpha,((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j);
						if (isChan(flattenedFieldTypes.get(j))) {
							fw.write("-1)+1;\n");
						} else {
							Assert.assertTrue(isPid(flattenedFieldTypes
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
			int proctypeIdentifier = proctypeId(proctypeName);
			fw.write("   j = applyToPr(*alpha," + j + ");\n");
			fw.write("   memcpy(SEG(&temp,j),SEG(s," + j + "),sizeof(P"
					+ proctypeIdentifier + "));\n");
			fw.write("   VAR(&temp,j,_pid,P" + proctypeIdentifier
					+ ")=VAR(s,j,_pid,P" + proctypeIdentifier + ");\n");
			fw.write("\n");
		}
	}

	private void permuteChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {
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
			if (isChan(flattenedFieldTypes.get(i))
					|| isPid(flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	/* Methods to apply a permutation to a state via transpositions */

	private void writeApplyPermToStateTranspositions(FileWriter fw)
			throws IOException {
		fw.write("void applyPermToState(State *s, ");
		fw.write("perm_t *alpha) {\n");
		fw.write("   int i;\n");
		fw.write("   for(i=0; i<alpha->prLength; i=i+2) {\n");
		fw.write("      applyPrSwapToState(s,alpha->pr[i],alpha->pr[i+1]);\n");
		fw.write("   }\n\n");
		fw.write("   for(i=0; i<alpha->chLength; i=i+2) {\n");
		fw.write("      applyChSwapToState(s,alpha->ch[i],alpha->ch[i+1]);\n");
		fw.write("   }\n\n");
		fw.write("}\n\n");
	}

	private void writeApplyChSwapToState(FileWriter fw) throws IOException {
		fw.write("void applyChSwapToState(State *s, int a, int b) {\n");
		fw.write("   uchar tempCid;\n");
		fw.write("   int slot;\n");
		swapProctypeLocalChVariables(fw);
		swapChannelChContents(fw);
		swapChannels(fw);
		fw.write("}\n\n");
	}

	private void writeApplyPrSwapToState(FileWriter fw) throws IOException {
		fw.write("void applyPrSwapToState(State *s, int a, int b) {\n");
		fw.write("   uchar tempPid;\n");
		fw.write("   int slot;\n");
		swapPrGlobal(fw);
		swapProctypeLocalPrVariables(fw);
		swapChannelPrContents(fw);
		swapProcesses(fw);
		fw.write("}\n\n");
	}

	private void swapPrGlobal(FileWriter fw) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
				.getTopEntries();

		String referencePrefix = "s->";

		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {

				if (!(Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS)) {
					for (SensitiveVariableReference reference : getSensitiveVariableReferences(
							name, ((VarEntry) entry).getType(), referencePrefix)) {
						Assert.assertTrue(isPid(reference.getType()));
						fw.write("   if(" + reference.getReference()
								+ "==a) {\n");
						fw.write("      " + reference.getReference()
								+ " = b;\n");
						fw.write("   } else if(" + reference.getReference()
								+ "==b) {\n");
						fw.write("      " + reference.getReference()
								+ " = a;\n");
						fw.write("   }\n");
					}
				}

				for (PidIndexedArrayReference reference : getSensitivelyIndexedArrayReferences(
						name, ((VarEntry) entry).getType(), referencePrefix)) {
					Assert.assertTrue(((ArrayType) reference.getType())
							.getIndexType() instanceof VisibleType);
					Assert.assertTrue(isPid((VisibleType) ((ArrayType) reference.getType())
							.getIndexType()));
					/* uchar must be changed to appropriate type */
					fw.write("   {\n");
					fw.write("       uchar temp;\n");
					fw.write("       temp = " + reference.getReference()
							+ "[a];\n");
					fw.write("       " + reference.getReference() + "[a] = "
							+ reference.getReference() + "[b];\n");
					fw.write("       " + reference.getReference()
							+ "[b] = temp;\n");
					fw.write("   }\n");
				}
			}
		}
	}

	private void swapProctypeLocalPrVariables(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			String referencePrefix = "((P" + proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo
					.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();
			List<SensitiveVariableReference> sensitivelyIndexedArrays = new ArrayList<SensitiveVariableReference>();

			Map<String, EnvEntry> localScope = proctype.getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter
					.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {
					referencesToPermute.addAll(getSensitiveVariableReferences(
							varName, ((VarEntry) localScope.get(varName))
									.getType(), referencePrefix));
					sensitivelyIndexedArrays
							.addAll(getSensitivelyIndexedArrayReferences(
									varName, ((VarEntry) localScope
											.get(varName)).getType(),
									referencePrefix));
				}
			}

			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				Assert.assertTrue(isPid(reference.getType())
						|| isChan(reference.getType()));
				if (isPid(reference.getType())) {
					fw.write("   if(" + reference.getReference() + "==a) {\n");
					fw.write("   " + reference.getReference() + " = b;\n");
					fw.write("   } else if(" + reference.getReference()
							+ "==b) {\n");
					fw.write("   " + reference.getReference() + " = a;\n");
					fw.write("   }\n");
				}
			}

			for (ListIterator iter = sensitivelyIndexedArrays.listIterator(); iter
					.hasNext();) {
				PidIndexedArrayReference reference = (PidIndexedArrayReference) iter
						.next();
				Assert.assertTrue(((ArrayType) reference.getType())
						.getIndexType() instanceof VisibleType);
				Assert.assertTrue(isPid((VisibleType) ((ArrayType) reference.getType())
						.getIndexType()));
				/* uchar must be changed to appropriate type */
				fw.write("   {\n");
				fw.write("       uchar temp;\n");
				fw
						.write("       temp = " + reference.getReference()
								+ "[a];\n");
				fw.write("       " + reference.getReference() + "[a] = "
						+ reference.getReference() + "[b];\n");
				fw
						.write("       " + reference.getReference()
								+ "[b] = temp;\n");
				fw.write("   }\n");
			}

			fw.write("\n");
		}

	}

	private void swapChannelChContents(FileWriter fw) throws IOException {
		for (int i = 0; i < typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (isChan(flattenedFieldTypes.get(j))) {
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

	private void swapChannelPrContents(FileWriter fw) throws IOException {

		for (int i = 0; i < typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsPidType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (isPid(flattenedFieldTypes.get(j))) {
						fw.write("      if(((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "==a) {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=b;\n");
						fw
								.write("      } else if(((Q" + (i + 1)
										+ " *)QSEG(s," + i
										+ "))->contents[slot].fld" + j
										+ "==b) {\n");
						fw.write("         ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=a;\n");
						fw.write("      }\n");
					}
				}
				fw.write("   }\n");
			}
		}

	}

	private void swapProctypeLocalChVariables(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			String referencePrefix = "((P" + proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo
					.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToPermute = new ArrayList<SensitiveVariableReference>();

			Map<String, EnvEntry> localScope = proctype.getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter
					.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {
					referencesToPermute.addAll(getSensitiveVariableReferences(
							varName, ((VarEntry) localScope.get(varName))
									.getType(), referencePrefix));
				}
			}

			for (ListIterator iter = referencesToPermute.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				Assert.assertTrue(isPid(reference.getType())
						|| isChan(reference.getType()));
				if (isChan(reference.getType())) {
					fw
							.write("   if(" + reference.getReference()
									+ "==a+1) {\n");
					fw.write("      " + reference.getReference() + " = b+1;\n");
					fw.write("   } else if(" + reference.getReference()
							+ "==b+1) {\n");
					fw.write("      " + reference.getReference() + " = a+1;\n");
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
		out.write("State min_now;\n\n");
		out
				.write("#define SEG(state,pid) (((uchar *)state)+proc_offset[pid])\n");
		out.write("#define QSEG(state,cid) (((uchar *)state)+q_offset[cid])\n");
		out
				.write("#define VAR(state,pid,var,type) ((type *)SEG(state,pid))->var\n");
		out
				.write("#define QVAR(state,cid,var,type) ((type *)QSEG(state,cid))->var\n\n");


	}

	private void replaceWithRepresentativeStore(List<String> lines, int counter) {
		lines.set(counter, lines.get(counter).replace("&now", "rep(&now)")); // If
		// "&now"
		// is
		// being
		// stored,
		// replace "&now" with "rep(&now)".
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

	private void dealWithSymmetryThreadFiles() throws IOException {
		if(Config.PTHREADS) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Copying files for multi-threaded symmetry reduction:");
			
			copyTextFile(Config.COMMON + "symmetry_threads.c", "symmetry_threads.c");
			copyTextFile(Config.COMMON + "symmetry_threads.h", "symmetry_threads.h");
		}
	}

	private void dealWithSegmentFiles() throws IOException {
		if(Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Copying files for segmented strategy:");
			
			copyTextFile(Config.COMMON + "segment.h", "segment.h");
		}
	}
	
	private void dealWithGroupFiles() throws IOException, InterruptedException {
		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Copying template files for computing with permutations:");
		
		if (!usingMarkers() && Config.USE_TRANSPOSITIONS) {
			copyTextFile(Config.COMMON + "groupTranspositions.c", "group.c");
			// Copy group theory files into current directory
			copyTextFile(Config.COMMON + "groupTranspositions.h", "group.h");
		} else if (!usingMarkers() && !Config.USE_TRANSPOSITIONS) {
			/* Copy group theory files into current directory */
			copyTextFile(Config.COMMON + "groupBasic.c", "group.c");
			copyTextFile(Config.COMMON + "groupBasic.h", "group.h");
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
			copyTextFile("pan." + ending, "sympan." + ending);
		}
	}

	private void writeMarkPID(FileWriter fw) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
				.getTopEntries();

		String referencePrefix = "s->";

		fw.write("void markPIDs(State* s, int* map) {\n");

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List sensitiveReferences = getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), referencePrefix);
				for (int i = 0; i < sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences
							.get(i);
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("   if(" + reference.getReference() + ">0) "
							+ reference.getReference() + " = map["
							+ reference.getReference() + "-1]+1;\n");
				}
			}
		}

		String proctypeName = typeInfo.getProctypeNames().get(0);
		ProctypeEntry proctype = (ProctypeEntry) typeInfo
				.getEnvEntry(proctypeName);
		Map<String, EnvEntry> localScope = proctype.getLocalScope();
		for (String varName : localScope.keySet()) {
			if (localScope.get(varName) instanceof VarEntry) {
				VisibleType entryType = ((VarEntry) localScope.get(varName)).getType();
				Assert.assertFalse(entryType instanceof ProductType);
				if (entryType instanceof PidType) {
					for (int j = 1; j < typeInfo.getNoProcesses(); j++) {
						fw.write("   if(((P" + proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName + ">0) "
								+ "((P" + proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName
								+ " = map[ " + "((P" + proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName
								+ "-1]+1;\n");
					}
				}
			}

		}

		List<String> staticChannelNames = typeInfo.getStaticChannelNames();
		int chanId = 0;
		for (String chanName : staticChannelNames) {
			ProductType msgType = (ProductType) ((ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry(chanName)).getType()).getMessageType();
			int chanLength = ((ChannelEntry) typeInfo.getEnvEntry(chanName))
					.getLength();
			for (int i = 0; i < msgType.getArity(); i++) {
				Assert.assertTrue(msgType.getTypeOfPosition(i) instanceof VisibleType);
				VisibleType fieldType = (VisibleType) msgType.getTypeOfPosition(i);

				Assert.assertFalse(fieldType instanceof ArrayType); // SPIN
				// doesn't
				// allow
				// this

				if (fieldType instanceof PidType) {
					for (int j = 0; j < chanLength; j++) {
						fw.write("   if(((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ ">0) " + "((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ "=map[((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ "-1]+1;\n");
					}
				}
			}
			chanId++;
		}
		
		/* NOW SWAP AROUND THE pid-indexed ARRAYS */

		fw.write("   uchar swapper[" + typeInfo.getNoProcesses() + "];\n");
		fw.write("   swapper[0] = 0;\n");
		fw.write("   int i;\n");
		
		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
			.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				if(((VarEntry)entry).getType() instanceof ArrayType && ((ArrayType)((VarEntry)entry).getType()).getIndexType() instanceof PidType) {
					fw.write("   for(i=1; i<" + typeInfo.getNoProcesses() + "; i++) swapper[i]=0;\n\n");
					
					for(int i=1; i<typeInfo.getNoProcesses(); i++) {
						fw.write("   swapper[map[" + (i-1) + "]+1] = s->" + name + "[" + i + "];\n");
					}

					fw.write("   memcpy(s->" + name + ",swapper," + typeInfo.getNoProcesses() + ");\n\n");
				
				}
			}
		}
			
		
		fw.write("}\n\n");

	}

	private void writeFlatten(FileWriter fw) throws IOException {
		fw.write("void flatten(State *s) {\n");
		writeFlattenSensitiveGlobals(fw);
		writeFlattenSensitiveLocals(fw);
		writeFlattenSensitiveChannels(fw);
		fw.write("}\n\n");
	}

	private void writeFlattenSensitiveChannels(FileWriter fw)
			throws IOException {
		for (int i = 0; i < typeInfo.getStaticChannelNames().size(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (containsPidType(flattenedFieldTypes)
					|| containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (isPid(flattenedFieldTypes.get(j))
							|| isChan(flattenedFieldTypes.get(j))) {
						fw.write("      ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=0;\n");
					}
				}
				fw.write("   }\n\n");
			}
		}
	}

	private void writeFlattenSensitiveLocals(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {
			String proctypeName = ((ProcessEntry) typeInfo.getProcessEntries()
					.get(j)).getProctypeName();
			String referencePrefix = "((P" + proctypeId(proctypeName)
					+ " *)SEG(s," + j + "))->";

			ProctypeEntry proctype = (ProctypeEntry) typeInfo
					.getEnvEntry(proctypeName);
			List<SensitiveVariableReference> referencesToFlatten = new ArrayList<SensitiveVariableReference>();

			Map<String, EnvEntry> localScope = proctype.getLocalScope();
			for (Iterator<String> iter = localScope.keySet().iterator(); iter
					.hasNext();) {
				String varName = iter.next();
				if (localScope.get(varName) instanceof VarEntry) {
					referencesToFlatten.addAll(getSensitiveVariableReferences(
							varName, ((VarEntry) localScope.get(varName))
									.getType(), referencePrefix));
				}
			}

			for (ListIterator iter = referencesToFlatten.listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				Assert.assertTrue(isPid(reference.getType())
						|| isChan(reference.getType()));
				fw.write("   " + reference.getReference() + " = 0;\n");
			}

			fw.write("\n");
		}
	}

	private void writeFlattenSensitiveGlobals(FileWriter fw) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
				.getTopEntries();

		String referencePrefix = "s->";

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List sensitiveReferences = getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), referencePrefix);
				for (int i = 0; i < sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences
							.get(i);
					Assert.assertTrue(isPid(reference.getType()));
					fw.write("   " + reference.getReference() + " = 0;\n");
				}
			}
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
			for (int j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {
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
		for (int i = 1; i <= typeInfo.getStaticChannelNames().size(); i++) {
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
					if (!(isChan(flattenedFieldTypes.get(k)) || isPid(flattenedFieldTypes
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

		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
		.getTopEntries();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if (entry instanceof VarEntry) {
				VisibleType entryType = ((VarEntry)entry).getType();
				if(entryType instanceof ArrayType && isPid((VisibleType) ((ArrayType)entryType).getIndexType()) &&
						(((ArrayType)entryType).getElementType() instanceof SimpleType)) {
					if(isPid(((ArrayType)entryType).getElementType())) {
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
							.addAll(getInsensitiveVariableReferences(varName,
									((VarEntry) localScope.get(varName))
											.getType(), ""));
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
		fw.write("int lt(State *s, State *t) {\n");
		fw.write("  int slot;\n\n");

		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
		.getTopEntries();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if (entry instanceof VarEntry) {
				VisibleType entryType = ((VarEntry)entry).getType();
				if(entryType instanceof ArrayType && isPid((VisibleType) ((ArrayType)entryType).getIndexType()) &&
						(((ArrayType)entryType).getElementType() instanceof SimpleType)) {
					for(int i=1; i<typeInfo.getNoProcesses(); i++) {
					
						if(isPid(((ArrayType)entryType).getElementType())) {
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
				String sPrefix = "((P" + proctypeId(proctypeName) + " *)SEG(s," + j
						+ "))->";
				String tPrefix = "((P" + proctypeId(proctypeName) + " *)SEG(t," + j
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
								.addAll(getInsensitiveVariableReferences(varName,
										((VarEntry) localScope.get(varName))
												.getType(), ""));
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

		for (j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {

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
					if (!(isChan(flattenedFieldTypes.get(k)) || isPid(flattenedFieldTypes
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

	private boolean containsPidType(List<VisibleType> flattenedFieldTypes) {
		for (int i = 0; i < flattenedFieldTypes.size(); i++) {
			if (isPid(flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	private boolean containsChanType(List<VisibleType> flattenedFieldTypes) {
		for (int i = 0; i < flattenedFieldTypes.size(); i++) {
			if (isChan(flattenedFieldTypes.get(i))) {
				return true;
			}
		}
		return false;
	}

	private boolean containsInsensitiveType(List<VisibleType> flattenedFieldTypes) {
		for (int i = 0; i < flattenedFieldTypes.size(); i++) {
			if (!(isPid(flattenedFieldTypes.get(i)) || isChan(flattenedFieldTypes
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
			int proctypeIdentifier = proctypeId(proctypeName);
			fw.write("   if(a==" + j + ") {\n");
			fw.write("      P" + proctypeIdentifier + " temp;\n");
			fw.write("      memcpy(&temp,SEG(s,a),sizeof(P"
					+ proctypeIdentifier + "));\n");
			fw.write("      memcpy(SEG(s,a),SEG(s,b),sizeof(P"
					+ proctypeIdentifier + "));\n");
			fw.write("      memcpy(SEG(s,b),&temp,sizeof(P"
					+ proctypeIdentifier + "));\n");
			fw.write("      tempPid = VAR(s,a,_pid,P" + proctypeIdentifier
					+ ");\n");
			fw.write("      VAR(s,a,_pid,P" + proctypeIdentifier
					+ ") = VAR(s,b,_pid,P" + proctypeIdentifier + ");\n");
			fw.write("      VAR(s,b,_pid,P" + proctypeIdentifier
					+ ") = tempPid;\n");
			fw.write("      return;\n");
			fw.write("   }\n\n");
		}
	}

	private void swapChannels(FileWriter fw) throws IOException {
		for (int j = 0; j < typeInfo.getStaticChannelNames().size(); j++) {
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
			fw.write("   };\n");
			fw.write("\n");
		}
	}

	protected int proctypeId(String proctypeName) {
		return typeInfo.getProctypeNames().indexOf(proctypeName);
	}

	protected List<PidIndexedArrayReference> getSensitivelyIndexedArrayReferences(
			String name, VisibleType type, String referencePrefix) {

		List<PidIndexedArrayReference> result = new ArrayList<PidIndexedArrayReference>();
		if (isArray(type)) {
			if (isPid((VisibleType) ((ArrayType) type).getIndexType())
					&& !isByte((VisibleType) ((ArrayType) type).getIndexType())) {
				result.add(new PidIndexedArrayReference(referencePrefix + name,
						(ArrayType) type));
			}
			for (int i = 0; i < ((ArrayType) type).getLength(); i++) {
				result.addAll(getSensitivelyIndexedArrayReferences(name + "["
						+ i + "]", ((ArrayType) type).getElementType(),
						referencePrefix));
			}
		} else if (isRecord(type)) {
			TypeEntry recordEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) type).name());
			for (Iterator iter = recordEntry.getFieldNames().iterator(); iter
					.hasNext();) {
				String fieldName = (String) iter.next();
				result.addAll(getSensitivelyIndexedArrayReferences(fieldName,
						recordEntry.getFieldType(fieldName), referencePrefix
								+ name + "."));
			}
		}

		return result;
	}

	protected List<SensitiveVariableReference> getSensitiveVariableReferences(
			String varName, VisibleType varType, String prefix) {
		List<SensitiveVariableReference> result = new ArrayList<SensitiveVariableReference>();
		if (isPid(varType) || isChan(varType)) {
			result
					.add(new SensitiveVariableReference(prefix + varName,
							varType));
		} else if (isArray(varType)) {
			for (int i = 0; i < ((ArrayType) varType).getLength(); i++) {
				result.addAll(getSensitiveVariableReferences(varName + "[" + i
						+ "]", ((ArrayType) varType).getElementType(), prefix));
			}
		} else if (isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) varType).name());
			for (Iterator iter = typeEntry.getFieldNames().iterator(); iter
					.hasNext();) {
				String fieldName = (String) iter.next();
				result.addAll(getSensitiveVariableReferences(fieldName,
						typeEntry.getFieldType(fieldName), prefix + varName
								+ "."));
			}
		}

		return result;
	}

	protected List<String> getInsensitiveVariableReferences(String varName,
			VisibleType varType, String prefix) {
		List<String> result = new ArrayList<String>();

		if (isPid(varType) || isChan(varType)) {
			return result;
		}

		if (isArray(varType)) {
			Assert.assertTrue(((ArrayType) varType).getIndexType() instanceof VisibleType);
			if (isPid((VisibleType) ((ArrayType) varType).getIndexType())) {
				return result;
			}

			for (int i = 0; i < ((ArrayType) varType).getLength(); i++) {
				result.addAll(getInsensitiveVariableReferences(varName + "["
						+ i + "]", ((ArrayType) varType).getElementType(),
						prefix));
				return result;
			}
		}

		if (isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry) typeInfo
					.getEnvEntry(((RecordType) varType).name());
			for (Iterator iter = typeEntry.getFieldNames().iterator(); iter
					.hasNext();) {
				String fieldName = (String) iter.next();
				result.addAll(getInsensitiveVariableReferences(fieldName,
						typeEntry.getFieldType(fieldName), prefix + varName
								+ "."));
			}
			return result;
		}

		result.add(prefix + varName);
		return result;

	}

	private String appendEq(String name, String eqMethod) {
		return eqMethod + "(m1->" + name + "==m2->" + name + ")&&";
	}

	private String appendLt(String name, String ltMarkersMethod) {
		return ltMarkersMethod + "   if(m1->" + name + "<m2->" + name
				+ ") return 1;\n   if(m1->" + name + ">m2->" + name
				+ ") return 0;\n";
	}

	private void writeMarkers(FileWriter fw) throws IOException {
		String markerStruct = "#define bitvector unsigned int\n#define SET_1(bv,i) bv=bv|(1<<i)\n\ntypedef struct Marker {\n";
		String markMethod = "void mark(Marker *marker, State* s, int i) {\n   int j;\n";
		String eqMethod = "int eq(Marker* m1, Marker* m2) {\n   return ";
		String ltMarkersMethod = "int lt_markers(Marker* m1, Marker* m2) {\n";
		String ltMethod = "int lt(Marker* markers, int i, int j, State* s) {\n" +
			"if(lt_markers(&markers[i],&markers[j])) return 1;\n" + 
			"if(lt_markers(&markers[j],&markers[i])) return 0;\n\n";
		
		Map<String, EnvEntry> globalVariables = typeInfo.getEnv()
				.getTopEntries();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
	
				VisibleType entryType = ((VarEntry) entry).getType();
	
				Assert.assertFalse(entryType instanceof ChanType);
				Assert.assertFalse(entryType instanceof ProductType);
	
				if (entryType instanceof ArrayType) {
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ChanType);
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ArrayType);
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ProductType);
	
					if (((ArrayType) entryType).getElementType() instanceof RecordType) {
						System.out
								.println("Markers do not currently support arrays of records");
						System.exit(0);
					}
	
					if (((ArrayType) entryType).getIndexType() instanceof PidType) {
						if (((ArrayType) entryType).getElementType() instanceof PidType) {
	
							
							markerStruct += "   uchar " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
	
							markerStruct += "   uchar " + name + "_selfloop;\n";
							eqMethod = appendEq(name + "_selfloop", eqMethod);
							ltMarkersMethod = appendLt(name + "_selfloop", ltMarkersMethod);
	
							markMethod += "   marker->" + name + " = 0;\n";
							markMethod += "   for(j=1; j<" + typeInfo.getNoProcesses()
									+ "; j++) {\n";
							markMethod += "      if(s->" + name + "[j]==i) marker->"
									+ name + "++;\n";
							markMethod += "   }\n";
							markMethod += "   if(s->" + name + "[i]==i) marker->"
									+ name + "_selfloop = 1; else marker->"
									+ name + "_selfloop = 0;\n";
							
							ltMethod += "   if(s->" + name + "[i+1]==0) {\n" +
								"      if(s->" + name + "[j+1]!=0) { return 1; }\n" +
								"   } else {" +
								"      if(lt_markers(&markers[s->" + name + "[i+1]-1],&markers[s->" + name + "[j+1]-1])) return 1;\n" +
								"      if(lt_markers(&markers[s->" + name + "[j+1]-1],&markers[s->" + name + "[i+1]-1])) return 0;\n  }\n\n";

							// TODO Need to add this code for local pid variables too.  Don't think we need it for non-pid arrays or non-pid locals.
							
						} else {
							markerStruct += "   uchar " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
							markMethod += "   marker->" + name + " = s->"
									+ name + "[i];\n";
						}
					} else {
						Assert.assertTrue(((ArrayType) entryType)
								.getIndexType() instanceof ByteType);
						if (((ArrayType) entryType).getElementType() instanceof PidType) {
							markerStruct += "   bitvector " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
							markMethod += "   marker->" + name + "=0;\n";
							for (int i = 0; i < ((ArrayType) entryType)
									.getLength(); i++) {
								markMethod += "   if(s->" + name + "[" + i
										+ "]==i) SET_1(marker->" + name + ","
										+ i + ");\n";
							}
						}
					}
	
				} else if (entryType instanceof PidType) {
					markerStruct += "   uchar " + name + " : 1;\n";
					eqMethod = appendEq(name, eqMethod);
					ltMarkersMethod = appendLt(name, ltMarkersMethod);
					markMethod += "   marker->" + name + " = s->" + name
							+ "==i ? 1 : 0;\n";
				} else if (entryType instanceof RecordType) {
					System.out
							.println("Markers do not currently support records");
					System.exit(0);
				}
	
			}
		}
	
		Assert.assertEquals(typeInfo.getProctypeNames().size(), 2);
	
		Assert.assertEquals(typeInfo.getProctypeNames().get(1),
				ProctypeEntry.initProctypeName);
	
		String proctypeName = typeInfo.getProctypeNames().get(0);
		ProctypeEntry proctype = (ProctypeEntry) typeInfo
				.getEnvEntry(proctypeName);
		Map<String, EnvEntry> localScope = proctype.getLocalScope();
		eqMethod = appendEq("_p", eqMethod);
		ltMarkersMethod = appendLt("_p", ltMarkersMethod);
		markerStruct += "   uchar _p;\n";
		markMethod += "   marker->_p = ((P" + proctypeId(proctypeName)
				+ " *)SEG(s,i))->_p;\n";
	
		for (String varName : localScope.keySet()) {
			if (localScope.get(varName) instanceof VarEntry) {
				VisibleType entryType = ((VarEntry) localScope.get(varName)).getType();
				Assert.assertFalse(entryType instanceof ProductType);
				if (entryType instanceof ArrayType) {
					System.out
							.println("Local array variables not yet supported with markers");
					System.exit(0);
				}
				if (entryType instanceof RecordType) {
					System.out
							.println("Local record variables not yet supported with markers");
					System.exit(0);
				}
	
				if (entryType instanceof PidType) {
					markerStruct += "   uchar " + varName + ";\n";
					eqMethod = appendEq(varName, eqMethod);
					ltMarkersMethod = appendLt(varName, ltMarkersMethod);
	
					markerStruct += "   uchar " + varName + "_selfloop;\n";
					eqMethod = appendEq(varName + "_selfloop", eqMethod);
					ltMarkersMethod = appendLt(varName + "_selfloop", ltMarkersMethod);
	
					markMethod += "   marker->" + varName + " = 0;\n";
					markMethod += "   for(j=1; j<" + typeInfo.getNoProcesses()
							+ "; j++) {\n";
					markMethod += "      if(((P" + proctypeId(proctypeName)
							+ " *)SEG(s,j))->" + varName + "==i) marker->"
							+ varName + "++;\n";
					markMethod += "   }\n";
					markMethod += "   if(((P" + proctypeId(proctypeName)
							+ " *)SEG(s,i))->" + varName + "==i) marker->"
							+ varName + "_selfloop = 1; else marker->"
							+ varName + "_selfloop = 0;\n";
				} else {
					markerStruct += "   uchar " + varName + ";\n";
					eqMethod = appendEq(varName, eqMethod);
					ltMarkersMethod = appendLt(varName, ltMarkersMethod);
					markMethod += "   marker->" + varName + " = ((P"
							+ proctypeId(proctypeName) + " *)SEG(s,i))->"
							+ varName + ";\n";
				}
			}
	
		}
	
		List<String> staticChannelNames = typeInfo.getStaticChannelNames();
		int chanId = 0;
		for (String chanName : staticChannelNames) {
			ProductType msgType = (ProductType) ((ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry(chanName)).getType()).getMessageType();
			int chanLength = ((ChannelEntry) typeInfo.getEnvEntry(chanName))
					.getLength();
			for (int i = 0; i < msgType.getArity(); i++) {
				Assert.assertTrue(msgType.getTypeOfPosition(i) instanceof VisibleType);
				VisibleType fieldType = (VisibleType) msgType.getTypeOfPosition(i);
	
				Assert.assertFalse(fieldType instanceof ArrayType); // SPIN
				// doesn't
				// allow
				// this
	
				if (fieldType instanceof RecordType) {
					System.out
							.println("Record fields on channels not yet supported with markers");
					System.exit(0);
				}
	
				if (fieldType instanceof PidType) {
					markerStruct += "   bitvector " + chanName + "_fld" + i
							+ ";\n";
					eqMethod = appendEq(chanName + "_fld" + i, eqMethod);
					ltMarkersMethod = appendLt(chanName + "_fld" + i, ltMarkersMethod);
				}
				markMethod += "   marker->" + chanName + "_fld" + i + "=0;\n";
				for (int j = 0; j < chanLength; j++) {
					markMethod += "   if( ((Q" + (chanId + 1) + "*)QSEG(s,"
							+ chanId + "))->contents[" + j + "].fld" + i
							+ "==i) SET_1(marker->" + chanName + "_fld" + i
							+ "," + j + ");\n";
				}
	
			}
			chanId++;
	
		}
	
		markerStruct += "} Marker;\n\n";
		markMethod += "}\n\n";
		ltMarkersMethod += "   return 0;\n}\n\n";
		/* Get rid of trailing && from eqMethod */
		eqMethod = eqMethod.substring(0, eqMethod.length() - 2) + ";\n}\n\n";
	
		ltMethod += "    return 0;\n\n}\n\n";
		
		fw.write(markerStruct);
		fw.write(markMethod);
		fw.write(ltMarkersMethod);
		fw.write(eqMethod);
		fw.write(ltMethod);
	}

	private boolean isRecord(VisibleType varType) {
		return varType instanceof RecordType;
	}

	private boolean isArray(VisibleType varType) {
		return varType instanceof ArrayType;
	}

	protected boolean isChan(VisibleType varType) {
		return varType instanceof ChanType;
	}

	protected static boolean isPid(VisibleType varType) {
		return varType instanceof PidType;
	}

	private static boolean isByte(VisibleType varType) {
		return varType instanceof ByteType;
	}

	private static void writeln(FileWriter fw, String s) throws IOException {
		fw.write(s + "\n");
	}

	private static String convertPerm(String alpha) {
		// Convert a GAP permutation into a permutation for SPIN
		return alpha.replace(',', ' ');
	}

	private static String compare(String x, String y) {
		if (Config.REDUCTION_STRATEGY == Strategy.SEGMENT) {
			return "lt(" + x + "," + y + ")";
		}
		return "memcmp(" + x + "," + y + ",vsize)<0";
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

	private static void copyTextFile(String sourceName, String destName)
			throws IOException {
		try {
			ProgressPrinter.print("   Copying " + sourceName + " -> " + destName + " ... ");
			BufferedReader br = new BufferedReader(new FileReader(sourceName));
			BufferedWriter bw = new BufferedWriter(new FileWriter(destName));
			String line;
			while ((line = br.readLine()) != null) {
				bw.write(line + "\n");
			}
			br.close();
			bw.close();
			ProgressPrinter.println("[OK]");
		} catch(FileNotFoundException e) {
			System.out.println("\n\nError: could not find file \"" + sourceName + "\".");
			System.exit(1);
		}
	}

}
