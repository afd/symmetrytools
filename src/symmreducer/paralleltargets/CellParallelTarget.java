package src.symmreducer.paralleltargets;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;

import src.utilities.Config;
import src.utilities.FileManager;
import src.utilities.StringOption;

public class CellParallelTarget implements ParallelTarget {

	public String getstartThreadsMethodName() {
		return "start_SPUs";
	}

	public void writeParallelIncludeLines(FileWriter out) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void writeThreadBodyBasic(FileWriter out, int numberOfNonTrivialGroupElements) throws IOException {
		createStateHeaderFile();
		
		writePPUThreadBodyBasic(out, numberOfNonTrivialGroupElements);
		writeSPUProgramBasic();
	}

	private void createStateHeaderFile() throws IOException {
		
		try {
			Process gcc = Runtime.getRuntime().exec("gcc -E sympan.h");
	
			String line;
			
			BufferedReader br = new BufferedReader(new InputStreamReader(gcc.getInputStream()));

			FileWriter out = new FileWriter("state.h");
			
			while((line = br.readLine()) != null) {

				if(line.length() > 16 &&  line.substring(0,16).equals("typedef struct P")) {
					do {
						out.write(line + "\n");
						line = br.readLine();
					} while(!(line.length()>3 && line.substring(0,3).equals("} P")));
					out.write(line + "\n\n");
				} else if( line.length() >= 22 && line.substring(0,22).equals("typedef struct State {")) {
					do {
						if(!(line.length()>0 && line.charAt(0)=='#')) {
							out.write(line + "\n");
						}
						line = br.readLine();
					} while(!(line.length()>=8 && line.substring(0,8).equals("} State;")));
					out.write(line + "\n\n");				
				}
				
			}
			gcc.waitFor();
			
			out.close();

		} catch(InterruptedException e) {
			System.out.println("Error while generating \"state.h\"");
			e.printStackTrace();
			System.exit(1);
		}
		
	}

	private void writeSPUProgramBasic() throws IOException {
		FileWriter out = new FileWriter("spu_minimise_state.h");
		out.write("void minimiseState() {\n");
		out.write("   int i;\n");
		out.write("   State temp;\n");
		out.write("   memcpy(&minimisedState, &originalState, vsize);\n\n");
		out.write("   for(i=myContext.start; i<myContext.end; i++) {\n");
		out.write("      memcpy(&temp, &originalState, vsize);\n");
		out.write("      applyPermToState(&temp, &(elementset_1[i]));\n");
		out.write("      if(memcmp(&temp,&minimisedState,vsize)<0) {\n");
		out.write("         memcpy(&minimisedState,&temp,vsize);\n");
		out.write("      }\n");
		out.write("   }\n\n");
		out.write("}\n\n");
		out.close();
	}

	public void writeThreadBodyStabiliserChain(FileWriter out, List<String> groupInfo) throws IOException {

		
		// TODO Auto-generated method stub
		
	}

	private void writePPUThreadBodyBasic(FileWriter out, final int numberOfNonTrivialGroupElements) throws IOException {
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

	public void copyFilesForMultiThreadedSymmetryReduction() throws IOException {
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_cell_ppu.c", "parallel_symmetry_cell_ppu.c");
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_cell_ppu.h", "parallel_symmetry_cell_ppu.h");
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_cell_spu.c", "parallel_symmetry_cell_spu.c");
		FileManager.copyTextFile(Config.getStringOption(StringOption.COMMON) + "parallel_symmetry_cell_spu.h", "parallel_symmetry_cell_spu.h");	
	}
	
	
}
