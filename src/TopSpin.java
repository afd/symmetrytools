package src;

import java.io.IOException;


import src.etch.checker.Check;
import src.symmextractor.SymmExtractor;
import src.symmreducer.SymmReducer;
import src.utilities.Config;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;

public class TopSpin {

	public static void main(String args[]) throws IOException, InterruptedException {

		if(args.length==0 || args.length>2 || (args.length==2 && !(args[0].equals("check")||args[0].equals("detect")))) {
			System.out.println("Usage: topspin [check,detect] <filename>");
			System.exit(0);
		}
		
		if(args.length==2 && args[0].equals("check")) {
			System.out.println("File: " + args[1]);
			System.out.println("Type-check only");
			Check check = new Check(args[1]);
		
			check.isWellTyped(true);
			System.exit(0);
		}

		Config.readConfigFile("config.txt");
		
		if(args.length==2 && args[0].equals("detect")) {
			Config.DETECT_ONLY = true;
			if(Config.PROFILE) { Profile.TOPSPIN_START = System.currentTimeMillis(); }
			Config.AUTOMATIC_DETECTION = true;
			System.out.println("File: " + args[1]);
			System.out.println("Detect symmetry only");
			System.out.println("Using " + Config.NO_CONJUGATES + " random conjugate" + (Config.NO_CONJUGATES==1?"":"s"));
			System.out.println("Timeout for finding largest valid subgroup: " + Config.TIME_BOUND + " seconds");

			if(Config.PROFILE) { Profile.TOPSPIN_START = System.currentTimeMillis(); }
			SymmExtractor extractor = new SymmExtractor(args[args.length-1]);
			extractor.extract();
			extractor.destroyGAP();
			if(Config.PROFILE) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
			System.exit(0);
		}

		ProgressPrinter.printSeparator();
		ProgressPrinter.println("TopSPIN version " + Config.VERSION);
		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Configuration settings:");
		ProgressPrinter.println("    Symmetry detection method: " + (Config.AUTOMATIC_DETECTION?"static channel diagram analysis":"manual"));
		if(!Config.AUTOMATIC_DETECTION) {
			ProgressPrinter.println("    Generators given in: " + Config.AUTOS_FILE);
		} else {
			ProgressPrinter.println("    Using " + Config.NO_CONJUGATES + " random conjugate" + (Config.NO_CONJUGATES==1?"":"s"));
			ProgressPrinter.println("    Timeout for finding largest valid subgroup: " + Config.TIME_BOUND + " seconds");
		}
		ProgressPrinter.println("    Reduction strategy: " + Config.REDUCTION_STRATEGY);
		ProgressPrinter.println("    Using transpositions to represent permutations: " + Config.USE_TRANSPOSITIONS);
		ProgressPrinter.println("    Using stabiliser chain for enumeration: " + Config.USE_STABILISER_CHAIN);
		ProgressPrinter.printSeparator();

		if(Config.PROFILE) { Profile.TOPSPIN_START = System.currentTimeMillis(); }
		SymmReducer reducer = new SymmReducer(args[args.length-1]);
		reducer.reduce();
		reducer.destroyGAP();
		if(Config.PROFILE) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
		
	}

}
