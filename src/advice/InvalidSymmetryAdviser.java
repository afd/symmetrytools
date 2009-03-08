package src.advice;

import java.io.FileWriter;
import java.io.IOException;

import src.group.Normaliser;
import src.group.Permutation;
import src.group.Permuter;
import src.promela.node.Node;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.utilities.Config;
import src.utilities.IntegerOption;
import src.utilities.ProgressPrinter;

public class InvalidSymmetryAdviser {

	private static int counter = 0;
	
	public static void explainWyNotSafeFor(Permutation perm, Node theAST, StaticChannelDiagramExtractor typeInfo) {
		
		if(counter >= Config.getIntegerOption(IntegerOption.EXPLAIN)) {
			return;
		}
		
		try {
			
			String originalFileName = counter + "_original.txt";
			FileWriter originalSpec = new FileWriter(originalFileName);
			String permutedFileName = counter + "_permuted.txt";
			FileWriter permutedSpec = new FileWriter(permutedFileName);

			if(Config.inVerboseMode()) {
				ProgressPrinter.println("        generating explanation in files " + originalFileName + " and " + permutedFileName);
			}
			
			
			counter++;
			
			Node originalAST = (Node) theAST.clone();
			theAST.apply(new Permuter(perm, typeInfo));
			Node permutedAST = (Node) theAST.clone();
			
			PromelaPrettyPrinter printerForOriginalAST = new PromelaPrettyPrinter();
			PromelaPrettyPrinter printerForPermutedAST = new PromelaPrettyPrinter();
			
			originalAST.apply(printerForOriginalAST);
			permutedAST.apply(printerForPermutedAST);
			
			String permString = perm.toString();
			
			originalSpec.write("Specification before applying " + permString + "\n\n");

			permutedSpec.write("Specification after applying " + permString + "\n\n");
			
			originalSpec.write(printerForOriginalAST.getString());
			permutedSpec.write(printerForPermutedAST.getString());

			originalAST.apply(new Normaliser(typeInfo.getNoProcesses()));
			permutedAST.apply(new Normaliser(typeInfo.getNoProcesses()));

			printerForOriginalAST = new PromelaPrettyPrinter();
			printerForPermutedAST = new PromelaPrettyPrinter();
			
			originalAST.apply(printerForOriginalAST);
			permutedAST.apply(printerForPermutedAST);
			
			
			originalSpec.write("\n\n\n\nSpecification after normalisation\n\n");
			permutedSpec.write("\n\n\n\nPermuted specification after normalisation\n\n");
			
			originalSpec.write(printerForOriginalAST.getString());
			permutedSpec.write(printerForPermutedAST.getString());
			
			theAST.apply(new Permuter(perm.inverse(), typeInfo));
			
			originalSpec.close();
			permutedSpec.close();
			
		} catch ( IOException e ) {
			System.out.println("IO error occured while trying to generate advice on invalid permutations.");
		}

	}

}
