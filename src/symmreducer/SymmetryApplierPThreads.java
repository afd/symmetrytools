package src.symmreducer;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;

import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.Strategy;
import src.utilities.StringHelper;

public class SymmetryApplierPThreads extends SymmetryApplier {

	public SymmetryApplierPThreads(String specification,
			StaticChannelDiagramExtractor typeInfo, String groupGenerators) {
		super(specification, typeInfo, groupGenerators);
	}
	
	protected void dealWithMainMethod(List<String> groupInfo, FileWriter out) throws IOException {
		out.write("   start_threads();\n\n");
	}

	
	protected void writeRepFunction(List<String> groupInfo, FileWriter out) throws IOException {
		if(Config.REDUCTION_STRATEGY==Strategy.ENUMERATE) {
			writeRepPthreadsEnumerate(groupInfo, out);
			return;
		}
		
		super.writeRepFunction(groupInfo, out);

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
	

}
