package src.utilities;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

public class FileManager {

	public static void copyTextFile(String sourceName, String destName) throws IOException {
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
