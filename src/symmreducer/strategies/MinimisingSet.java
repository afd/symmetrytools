package src.symmreducer.strategies;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import src.symmreducer.SymmetryApplier;
import src.utilities.StringHelper;

public class MinimisingSet {

	public static void writeRep(List<String> groupInfo, FileWriter out,
			int groupInfoCounter, int setCounter) throws IOException {
		int setSize = Integer.parseInt(StringHelper.trimWhitespace(groupInfo
				.get(groupInfoCounter + 1)));
		out.write("   {\n");
		out.write("      int j;\n");
		out.write("      " + SymmetryApplier.stateType + " current_min, tmp_now;\n");
		out.write("      do {\n");
		out.write("         " + SymmetryApplier.memoryCopy + "(&current_min,&min_now,vsize);\n\n");
		out.write("         for(j=0; j<" + setSize + "; j++) {\n");
		out.write("            " + SymmetryApplier.memoryCopy + "(&tmp_now,&min_now,vsize);\n");
		out.write("            applyPermToState(&tmp_now,&(elementset_"
				+ setCounter + "[j]));\n");
		// this could probably be made more efficient
		out.write("            if(" + SymmetryApplier.compare("&tmp_now", "&min_now") + ") {\n");
		out.write("               " + SymmetryApplier.memoryCopy + "(&min_now,&tmp_now,vsize);\n");
		out.write("            }\n");
		out.write("         }\n");
		out.write("      } while(" + SymmetryApplier.memoryCompare + "(&min_now,&current_min,vsize)!=0);\n\n");
		out.write("   }\n");
	}

}
