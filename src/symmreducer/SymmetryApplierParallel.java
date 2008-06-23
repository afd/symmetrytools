package src.symmreducer;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import junit.framework.Assert;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.ProgressPrinter;
import src.utilities.Strategy;
import src.utilities.StringHelper;

public class SymmetryApplierParallel extends SymmetryApplier {
	
	public SymmetryApplierParallel(String specification,
			StaticChannelDiagramExtractor typeInfo, String groupGenerators) {
		super(specification, typeInfo, groupGenerators);
	}
	
	@Override
	protected void dealWithMainMethod(List<String> groupInfo, FileWriter out) throws IOException {
		super.dealWithMainMethod(groupInfo, out);
		out.write("   " + Config.parallelTarget.getstartThreadsMethodName() + "();\n\n");
	}
	
	@Override
	protected void writeRepFunction(List<String> groupInfo, FileWriter out) throws IOException {
		
		if(Config.REDUCTION_STRATEGY==Strategy.ENUMERATE) {
			writeRepEnumerate(groupInfo, out);
			return;
		}
		
		super.writeRepFunction(groupInfo, out);

	}	

	@Override
	protected void writeParallelIncludeLines(FileWriter out) throws IOException {
		Config.parallelTarget.writeParallelIncludeLines(out);
	}
	
	
	private void dealWithSymmetryThreadFiles() throws IOException {
		if(Config.PARALLELISE) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Copying files for multi-threaded symmetry reduction:");

			Config.parallelTarget.copyFilesForMultiThreadedSymmetryReduction();
		}
	}

	@Override
	public void applySymmetry() {
		super.applySymmetry();
		try {
			dealWithSymmetryThreadFiles();
		} catch (Exception e) {
			System.out
					.println("An error occurred while generating files for parallel symmetry reduction.");
			e.printStackTrace();
			System.exit(1);
		}
	}


	private void writeRepEnumerate(List<String> groupInfo, FileWriter out) throws IOException {
		Assert.assertTrue(Config.REDUCTION_STRATEGY==Strategy.ENUMERATE);

		out.write(stateType + "* original;\n\n");

		out.write("void * thread_body(void* arg) {\n");
		out.write("   int id, start, end, i;\n");
	
		if(Config.USE_STABILISER_CHAIN) {
			Config.parallelTarget.writeThreadBodyStabiliserChain(out, groupInfo);
		} else {
			Config.parallelTarget.writeThreadBodyBasic(out, Integer.parseInt(StringHelper.trimWhitespace(groupInfo.get(1))));
		}

		out.write("   return 0;\n\n");
		out.write("}\n\n\n");

		if(Config.VECTORIZE_ID_SWAPPING) {
			out.write("AugmentedState orig_now_augmented;\n\n");
		}
		
		
		out.write("State *rep(State *orig_now) {\n");

		if(Config.VECTORIZE_ID_SWAPPING) {
			
			out.write("   memcpy(&orig_now_augmented.state, orig_now, vsize);\n");
			out.write("   extractIdentifierVariables(&orig_now_augmented);\n");
		    out.write("   augmented_memcpy(&min_now,&orig_now_augmented, vsize);\n");
		    out.write("   original = &orig_now_augmented;\n");
						
		} else {
			out.write("   memcpy(&min_now,orig_now, vsize);\n");
			out.write("   original = orig_now;\n");
		}
		
		out.write("   wake_threads();\n");
		out.write("   wait_for_threads();\n");

		if(Config.VECTORIZE_ID_SWAPPING) {
			out.write("   replaceIdentifierVariables(&min_now);\n");
			out.write("   return &min_now.state;\n");
		} else {
			out.write("   return &min_now;\n");
		}

		out.write("}\n\n");
				
	}

	
}
