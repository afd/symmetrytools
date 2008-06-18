package src.symmreducer.paralleltargets;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

public interface ParallelTarget {

	public String getstartThreadsMethodName();

	public void writeParallelIncludeLines(FileWriter out) throws IOException;

	public void writeThreadBodyBasic(FileWriter out, final int numberOfNonTrivialGroupElements) throws IOException;
	
	public void writeThreadBodyStabiliserChain(FileWriter out, List<String> groupInfo) throws IOException;

	public void copyFilesForMultiThreadedSymmetryReduction() throws IOException;
	
}
