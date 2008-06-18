package src.symmreducer.paralleltargets;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import src.symmreducer.SymmetryApplier;
import src.utilities.Config;
import src.utilities.StringHelper;

public class StabiliserChainEnumeration {

	public static void outputSimsEnumeration(FileWriter out, int setCounter, final int stabiliserChainSize, List<String> start, List<String> end, String minName, String originalName) throws IOException {
		
		out.write("   int ");
		for (int counter = 0; counter < stabiliserChainSize; counter++) {
			out.write("i" + counter);
			if (counter < (stabiliserChainSize - 1)) {
				out.write(", ");
			} else {
				out.write(";\n\n");
			}
		}
		out.write("   " + SymmetryApplier.stateType + " partialImages[" + stabiliserChainSize + "];\n\n");

		writeSimsEnumerationForLoops(out, setCounter, stabiliserChainSize, start, end, minName, originalName);

	}

	private static void writeSimsEnumerationForLoop(FileWriter out, int setCounter, int level, final int stabiliserChainSize, List<String> start, List<String> end, String minName, String originalName) throws IOException {
		StringHelper.indent(out, level+1);
		
		int partitionIndex = stabiliserChainSize - level - 1;

		out.write("for(i" + partitionIndex + "=" + start.get(partitionIndex) + "; ");
		out.write("(i" + partitionIndex + "<" + end.get(partitionIndex) + ")");
		
		if(Config.PARALLELISE) {
			out.write(" && (count<(end-start))");			
		}
		
		out.write("; i" + partitionIndex + "++) {\n");
		
		StringHelper.indent(out, level+2);

		out.write(SymmetryApplier.memoryCopy + "(&partialImages[" + partitionIndex + "],");
		if (level == 0) {
			out.write(originalName);
		} else {
			out.write("&partialImages[" + (partitionIndex + 1) + "]");
		}
		out.write(",vsize);\n");
		
		StringHelper.indent(out,level+2);

		out.write("applyPermToState(&partialImages[" + partitionIndex
				+ "],&elementset_" + setCounter + "[" + partitionIndex
				+ "][i" + partitionIndex + "]);\n\n");
		
		
		if(level < stabiliserChainSize-1) {
			writeSimsEnumerationForLoop(out, setCounter, level+1, stabiliserChainSize, start, end, minName, originalName);
		} else {
		
			if(Config.PARALLELISE) {
				StringHelper.indent(out, stabiliserChainSize+1);
				out.write("count++;\n");
			}
			
			StringHelper.indent(out,stabiliserChainSize+1);
			out	.write("if(" + SymmetryApplier.compare("&partialImages[0]", "&" + minName) + ") {\n");
	
			StringHelper.indent(out, stabiliserChainSize+2);
			out.write(SymmetryApplier.memoryCopy + "(&" + minName + ",&partialImages[0],vsize);\n");
	
			StringHelper.indent(out,stabiliserChainSize+1);
			out.write("}\n");

		}	
		
		StringHelper.indent(out, level);
		out.write("}\n");
	
	}

	private static void writeSimsEnumerationForLoops(FileWriter out, int setCounter, final int stabiliserChainSize, List<String> start, List<String> end, String minName, String originalName) throws IOException {
		writeSimsEnumerationForLoop(out, setCounter, 0, stabiliserChainSize, start, end, minName, originalName);
	}
	
	public static int getSizeOfStabiliserChain(List<String> groupInfo, int groupInfoCounter) {
		int stabChainSize = Integer.parseInt(StringHelper
				.trimWhitespace(groupInfo.get(groupInfoCounter + 1)));
		return stabChainSize;
	}
	
	public static List<Integer> getStabiliserChainComponentSizes(List<String> groupInfo, int groupInfoCounter, int stabChainSize) {
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
	
		
}
