package src;

import java.io.IOException;


import src.etch.checker.Check;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;
import src.symmextractor.SymmExtractor;
import src.symmreducer.SymmReducer;
import src.symmreducer.paralleltargets.CellParallelTarget;
import src.symmreducer.paralleltargets.ParallelTarget;
import src.symmreducer.paralleltargets.PthreadsParallelTarget;
import src.symmreducer.vectortargets.CellSPUVectorTarget;
import src.symmreducer.vectortargets.DummyVectorTarget;
import src.symmreducer.vectortargets.PowerPCVectorTarget;
import src.symmreducer.vectortargets.VectorTarget;
import src.utilities.AbsentConfigurationFileException;
import src.utilities.BadConfigurationFileException;
import src.utilities.BooleanOption;
import src.utilities.CommandLineSwitch;
import src.utilities.Config;
import src.utilities.IntegerOption;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;
import src.utilities.Strategy;
import src.utilities.StrategyOption;
import src.utilities.StringOption;

public class TopSpin {
	
	public static VectorTarget vectorTarget;
	public static ParallelTarget parallelTarget;

	public static final String VERSION = "2.2.4";
	
	public static void main(String args[]) throws IOException, InterruptedException, BadConfigurationFileException, AbsentConfigurationFileException, ParserException, LexerException {

		Config.initialiseCommandLineSwitches();
		
		if((args.length > 0) && (args[0].toUpperCase().equals("HELP"))) {
			processHelpArguments(args);
			System.exit(0);
		}

		int currentArg = Config.processCommandLineSwitches(args);
		
		if(currentArg >= args.length) {
			System.out.println("Error: no input file specified.\n");
			System.out.println("To run TopSPIN on an input file:\n" +
					           "    [command-line options] <inputfile>\n" +
							   "For help on command-line or config file option:\n" +
							   "    help <option>\n" +
							   "For list of options:\n" +
							   "    help\n");
			System.exit(1);
		}
		
		String specificationFile = args[currentArg];

		if((args.length-currentArg) > 1) {
			System.out.println("Warning: using argument " + (currentArg+1) + ", \"" + specificationFile + "\", as command line argument, ignoring remaining arguments.");
		}
		
		System.out.println("File: " + specificationFile);

		if(Config.commandLineSwitchIsSet(CommandLineSwitch.CHECK)) {
			Config.resetConfiguration();
			Config.setUnspecifiedOptionsToDefaultValues();
			System.out.println("Type-check only");
			new Check(specificationFile).typecheck();
			System.exit(0);
		}

		Config.readConfigFile("config.txt", true, true);
		dealWithVectorAndParallelSettings();
		
		if(Config.commandLineSwitchIsSet(CommandLineSwitch.DETECT)) {
			SymmExtractor extractor = new SymmExtractor(specificationFile);
			doAutomaticSymmetryDetection(specificationFile, extractor);
		} else {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("TopSPIN version " + VERSION);
			ProgressPrinter.printSeparator();
			Config.printConfiguration();
			ProgressPrinter.printSeparator();
	
			if(Config.profiling()) { Profile.TOPSPIN_START = System.currentTimeMillis(); }
	
			SymmReducer reducer = new SymmReducer(specificationFile);
	
			doAutomaticSymmetryReduction(reducer);
	
			if(Config.profiling()) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
		}
		
	}

	private static void processHelpArguments(String[] args) {
		
		assert(args.length>0);

		Config.resetConfiguration();
		
		if(args.length==1) {
			System.out.println("\nUse 'help' followed by name of config file or command-line option for summary of what the option does.\n");

			System.out.println("Available options:\n");

			System.out.println("Command line switches");
			System.out.println("=====================");
			for(CommandLineSwitch option : CommandLineSwitch.values()) {
				System.out.println("  -" + option.toString().toLowerCase());
			}
			System.out.println("\nBoolean config file");
			System.out.println("===================");
			
			for(BooleanOption option : BooleanOption.values()) {
				System.out.println("  " + option.toString().toLowerCase());
			}
			
			System.out.println("\nInteger config file options");
			System.out.println("===========================");

			for(IntegerOption option : IntegerOption.values()) {
				System.out.println("  " + option.toString().toLowerCase());
			}

			System.out.println("\nString config file options");
			System.out.println("==========================");

			for(StringOption option : StringOption.values()) {
				System.out.println("  " + option.toString().toLowerCase());
			}

			// A strategy option is really just a string option
			for(StrategyOption option : StrategyOption.values()) {
				System.out.println("  " + option.toString().toLowerCase());
			}
			
		} else {
			Config.showHelpForConfigurationOption(args[1], false);
		}
	}

	public static void doAutomaticSymmetryReduction(SymmReducer reducer) throws IOException, InterruptedException, ParserException, LexerException {
		reducer.reduce();
		reducer.destroyGAP();
	}

	public static void doAutomaticSymmetryDetection(String filename, SymmExtractor extractor) throws IOException, InterruptedException, ParserException, LexerException {
		if(Config.profiling()) { Profile.TOPSPIN_START = System.currentTimeMillis(); }
		ProgressPrinter.println("File: " + filename);
		ProgressPrinter.println("Detect symmetry only");
		ProgressPrinter.println("Using " + Config.getIntegerOption(IntegerOption.CONJUGATES) + " random conjugate" + (Config.getIntegerOption(IntegerOption.CONJUGATES)==1?"":"s"));
		ProgressPrinter.println("Timeout for finding largest valid subgroup: " + Config.getIntegerOption(IntegerOption.TIMEBOUND) + " seconds");
		extractor.extract();
		extractor.destroyGAP();
		if(Config.profiling()) { Profile.TOPSPIN_END = System.currentTimeMillis(); Profile.show(); }
	}

	
	public static void dealWithVectorAndParallelSettings() {
		if(Config.getBooleanOption(BooleanOption.VECTORISE)) {
			if(!Config.getBooleanOption(BooleanOption.TRANSPOSITIONS)) {
				ProgressPrinter.println("Vectorisation can only be applied when transpositions are used.  Vectorisation has been turned off.");
				Config.setBooleanOption(BooleanOption.VECTORISE, false);
			}
			if(Config.strategy()==Strategy.FLATTEN) {
				ProgressPrinter.println("Vectorisation is not compatible with the FLATTEN strategy.  Vectorisation has been turned off.");
				Config.setBooleanOption(BooleanOption.VECTORISE, false);
			}
		}

		String target = Config.getStringOption(StringOption.TARGET);

		if(null != target) {

			target = target.toUpperCase();
			
			if(target.equals("PC")) {
				vectorTarget = new DummyVectorTarget();
				parallelTarget = new PthreadsParallelTarget();
			} else if(target.equals("POWERPC")) {
				vectorTarget = new PowerPCVectorTarget();
				parallelTarget = new PthreadsParallelTarget();
			} else if(target.equals("CELL")) {
				vectorTarget = new CellSPUVectorTarget();
				parallelTarget = new CellParallelTarget();
			} else {
				System.out.println("Unknown target '" + target + "' specified in config.txt.  Defaulting to PC target.");
				vectorTarget = new DummyVectorTarget();
				parallelTarget = new PthreadsParallelTarget();
			}
			
		}
		
	}
	
}
