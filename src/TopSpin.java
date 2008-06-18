package src;

import java.io.IOException;


import src.etch.checker.Check;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;
import src.symmextractor.SymmExtractor;
import src.symmreducer.SymmReducer;
import src.utilities.AbsentConfigurationFileException;
import src.utilities.BadConfigurationFileException;
import src.utilities.Config;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;

public class TopSpin {

	public static void main(String args[]) throws IOException, InterruptedException, BadConfigurationFileException, AbsentConfigurationFileException, ParserException, LexerException {

		if(args.length==0 || args.length>2 || (args.length==2 && !(args[0].equals("check")||args[0].equals("detect")))) {
			System.out.println("");
			System.out.println("Usage: topspin [check,detect] <filename>");
			
			Config.printOptions();

			System.exit(0);
		}
		
		if(args.length==2 && args[0].equals("check")) {
			System.out.println("File: " + args[1]);
			System.out.println("Type-check only");
			Check check = new Check(args[1]);
		
			check.typecheck(true);
			System.exit(0);
		}

		Config.readConfigFile("config.txt");
		
		if(args.length==2 && args[0].equals("detect")) {

			SymmExtractor extractor = new SymmExtractor(args[args.length-1]);
			if(Config.PROFILE) { Profile.TOPSPIN_START = System.currentTimeMillis(); }

			doAutomaticSymmetryDetection(args[1], extractor);

			if(Config.PROFILE) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
			System.exit(0);
		}

		ProgressPrinter.printSeparator();
		ProgressPrinter.println("TopSPIN version " + Config.VERSION);
		ProgressPrinter.printSeparator();
		Config.printConfiguration();
		ProgressPrinter.printSeparator();

		if(Config.PROFILE) { Profile.TOPSPIN_START = System.currentTimeMillis(); }

		SymmReducer reducer = new SymmReducer(args[args.length-1]);

		doAutomaticSymmetryReduction(reducer);

		if(Config.PROFILE) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
		
	}

	public static void doAutomaticSymmetryReduction(SymmReducer reducer) throws IOException, InterruptedException {
		reducer.reduce();
		reducer.destroyGAP();
	}

	public static void doAutomaticSymmetryDetection(String filename, SymmExtractor extractor) throws IOException, InterruptedException {
		Config.DETECT_ONLY = true;
		Config.AUTOMATIC_DETECTION = true;
		
		ProgressPrinter.println("File: " + filename);
		ProgressPrinter.println("Detect symmetry only");
		ProgressPrinter.println("Using " + Config.NO_CONJUGATES + " random conjugate" + (Config.NO_CONJUGATES==1?"":"s"));
		ProgressPrinter.println("Timeout for finding largest valid subgroup: " + Config.TIME_BOUND + " seconds");
		extractor.extract();
		extractor.destroyGAP();
	}

}
