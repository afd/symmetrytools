package src.symmreducer.paralleltargets;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import src.symmreducer.SymmetryApplier;
import src.symmreducer.strategies.StabiliserChainEnumeration;
import src.utilities.Config;
import src.utilities.FileManager;
import src.utilities.StringOption;

public class PthreadsParallelTarget implements ParallelTarget {

	public String getstartThreadsMethodName() {
		return "start_threads";
	}

	public void writeThreadBodyBasic(FileWriter out, final int numberOfNonTrivialGroupElements) throws IOException {
		out.write("   id = *(int*)arg;\n");
		out.write("   get_data_section(&start, &end, id, " + numberOfNonTrivialGroupElements + ");\n\n");

		out.write("   while(working(id)) {\n");
		out.write("      " + SymmetryApplier.stateType + " partial_min;\n");
		out.write("      " + SymmetryApplier.stateType + " temp;\n");
		out.write("      " + SymmetryApplier.memoryCopy + "(&partial_min, original, vsize);\n\n");

		out.write("      for(i=start; i<end; i++) {\n");
		out.write("         " + SymmetryApplier.memoryCopy + "(&temp, original, vsize);\n");
		out.write("         applyPermToState(&temp, &(elementset_1[i]));\n");
		out.write("         if(" + SymmetryApplier.memoryCompare + "(&temp,&partial_min,vsize)<0) {\n");
		out.write("            " + SymmetryApplier.memoryCopy + "(&partial_min,&temp,vsize);\n");
		out.write("         }\n");
		out.write("      }\n\n");

		out.write("      pthread_mutex_lock(&min_mutex);\n");
		out.write("      if(" + SymmetryApplier.memoryCompare + "(&partial_min, &min_now, vsize)<0) {\n");
		out.write("         " + SymmetryApplier.memoryCopy + "(&min_now, &partial_min, vsize);\n");
		out.write("      }\n");
		out.write("      pthread_mutex_unlock(&min_mutex);\n");
		out.write("      topspin_thread_sleep(id);\n");
		out.write("   }\n\n");

	}

	public void writeThreadBodyStabiliserChain(FileWriter out, List<String> groupInfo) throws IOException {

		final int stabiliserChainSize = StabiliserChainEnumeration.getSizeOfStabiliserChain(groupInfo, 0);

		List<Integer> stabiliserChainComponentSizes = StabiliserChainEnumeration.getStabiliserChainComponentSizes(groupInfo, 0, stabiliserChainSize);

		int numberOfGroupElements = getSizeOfGroupFromStabiliserChainComponentSizes(stabiliserChainComponentSizes);

		out.write("   int ");
		for(int i=0; i<stabiliserChainSize; i++) {
			out.write("start_" + i + ", ");
		}
		out.write("count;\n");
		
		out.write("   id = *(int*)arg;\n");
		out.write("   get_data_section(&start, &end, id, " + numberOfGroupElements + ");\n\n");
		
		out.write("   while(working(id)) {\n");
		out.write("      " + SymmetryApplier.stateType + " partial_min;\n");
		out.write("      " + SymmetryApplier.memoryCopy + "(&partial_min, original, vsize);\n\n");

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

		StabiliserChainEnumeration.outputSimsEnumeration(out, 1, stabiliserChainSize, start, end, "partial_min", "original");

		out.write("      pthread_mutex_lock(&min_mutex);\n");
		out.write("      if(" + SymmetryApplier.memoryCompare + "(&partial_min, &min_now, vsize)<0) {\n");
		out.write("         " + SymmetryApplier.memoryCopy + "(&min_now, &partial_min, vsize);\n");
		out.write("      }\n");
		out.write("      pthread_mutex_unlock(&min_mutex);\n");
		out.write("      topspin_thread_sleep(id);\n");
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

	public void writeParallelIncludeLines(FileWriter out) throws IOException {
		out.write("\n#include \"parallel_symmetry_pthreads.h\"\n\n");
		out.write("pthread_mutex_t min_mutex = PTHREAD_MUTEX_INITIALIZER;\n\n");
	}

	public void copyFilesForMultiThreadedSymmetryReduction() throws IOException {
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_pthreads.c", "parallel_symmetry_pthreads.c");
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_pthreads.h", "parallel_symmetry_pthreads.h");
	}
		
}
