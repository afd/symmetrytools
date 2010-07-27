package src.symmreducer.testing;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.StringTokenizer;

import src.TopSpin;
import src.etch.testing.EtchTestCase;
import src.etch.testing.EtchTestOutcome;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;
import src.symmextractor.testing.SymmExtractorFailTestOutcome;
import src.symmextractor.testing.SymmExtractorRunTestOutcome;
import src.symmextractor.testing.SymmExtractorTestCase;
import src.symmextractor.testing.SymmExtractorTestOutcome;
import src.symmreducer.SymmReducer;
import src.testing.SystemErrorTestOutcome;
import src.testing.TestOutcome;
import src.utilities.AbsentConfigurationFileException;
import src.utilities.BadConfigurationFileException;
import src.utilities.BooleanOption;
import src.utilities.Config;
import src.utilities.ErrorStreamHandler;

public class SymmReducerTestCase extends SymmExtractorTestCase {

	private int searchDepth;
	private String compilerDirectives;

	public SymmReducerTestCase(String foldername, String modelFilename, SymmReducerTestOutcome expectedOutcome, String compilerDirectives, int searchDepth) {
		super(foldername, modelFilename, expectedOutcome);
		this.compilerDirectives = compilerDirectives;
		this.searchDepth = searchDepth;
	}

	public SymmReducerTestCase(String foldername, String modelFilename, SymmExtractorTestOutcome expectedOutcome) {
		super(foldername, modelFilename, expectedOutcome);
	}
	
	public SymmReducerTestCase(String foldername, String modelFilename, SymmReducerTestOutcome expectedOutcome, int searchDepth) {
		this(foldername, modelFilename, expectedOutcome, "", searchDepth);
	}

	public SymmReducerTestCase(String foldername, String modelFilename, SymmReducerTestOutcome expectedOutcome) {
		this(foldername, modelFilename, expectedOutcome, 10000);
	}
	
	public SymmReducerTestCase(String foldername, String modelFilename, SymmReducerTestOutcome expectedOutcome, String compilerDirectives) {
		this(foldername, modelFilename, expectedOutcome, compilerDirectives, 10000);
	}

	public SymmReducerTestCase(String foldername, String modelFilename, SymmReducerFailTestOutcome expectedOutcome, String compilerDirectives) {
		super(foldername, modelFilename, expectedOutcome);
		this.compilerDirectives = compilerDirectives;
		this.searchDepth = -1;
	}

	@Override
	public void run() {

		Config.initialiseCommandLineSwitches();

		try {

			EtchTestCase etchTest = new EtchTestCase(filename, EtchTestOutcome.WellTyped);
			
			etchTest.run();

			
			if(!etchTest.isPass()) {
				actualOutcome = etchTest.getOutcome();
			} else {
			
				Config.readConfigFile("symmextractor_common_config.txt", true, false);

				Config.readConfigFile(foldername + "config.txt", false, true);

				TopSpin.dealWithVectorAndParallelSettings();
				
				SymmReducer reducer = new SymmReducer(filename);

				TopSpin.doAutomaticSymmetryReduction(reducer);

				if(!reducer.isWellTyped()) {
					actualOutcome = SymmExtractorFailTestOutcome.BreaksRestrictions;
				} else if(!reducer.obeysSymmetryRestrictions) {
					actualOutcome = SymmExtractorFailTestOutcome.BreaksRestrictions;
				} else {

					if(null != (actualOutcome = compileSympanFiles())) {
						return;
					}

					actualOutcome = runVerifier(reducer);
				}
			}

		} catch(IOException e) {
			
			actualOutcome = SystemErrorTestOutcome.IOError;
			
		} catch (InterruptedException e) {

			actualOutcome = SystemErrorTestOutcome.InterruptedError;

		} catch (BadConfigurationFileException e) {

			actualOutcome = SystemErrorTestOutcome.BadConfigurationFile;

		} catch (AbsentConfigurationFileException e) {

			actualOutcome = SystemErrorTestOutcome.NoConfigurationFileFound;

		} catch (ParserException e) {

			actualOutcome = EtchTestOutcome.ParserError;

		} catch (LexerException e) {

			actualOutcome = EtchTestOutcome.ParserError;

		}
		
	}

	private static final String EXECUTABLE = "__topspinmain__";
	
	private TestOutcome runVerifier(SymmReducer reducer) {

		Process sympan;
		try {
			sympan = Runtime.getRuntime().exec(((!Config.isOSWindows()) ? "./" : "") + EXECUTABLE + " -m" + searchDepth);
		} catch (IOException e1) {
			return SymmReducerFailTestOutcome.VerificationIOError;
		}
		
		// Had to put this line in to stop the program from hanging.  Not sure why.
		BufferedReader br = new BufferedReader(new InputStreamReader(sympan.getInputStream()));

		int numberOfStates = 0;
		int numberOfTransitions = 0;
		
		String line;

		try
		{
			while((line = br.readLine())!=null) {
				
				// Uncomment to get the SPIN output for test cases
				//System.out.println(line);
				
				if(line.contains(" states, stored")) {
					numberOfStates = Integer.parseInt(new StringTokenizer(line, " ").nextToken());
				} else if(line.contains(" transitions (= stored+matched)")) {
					numberOfTransitions = Integer.parseInt(new StringTokenizer(line, " ").nextToken());
				}
			
			}
		} catch(NumberFormatException e) {
			sympan.destroy();
			return SymmReducerFailTestOutcome.ErrorParsingVerificationResult;
		} catch (IOException e) {
			return SymmReducerFailTestOutcome.VerificationIOError;
		}

		try {
			sympan.waitFor();
		} catch (InterruptedException e) {
			return SymmReducerFailTestOutcome.VerificationInterrupted;
		}

		if(0 != sympan.exitValue()) {
			return SymmReducerFailTestOutcome.VerificationFailure;
		}

		return new SymmReducerTestOutcome(
				new SymmExtractorRunTestOutcome(true, reducer.getSizeOfGroup(), reducer.requiredCosetSearch()), 
				numberOfStates, numberOfTransitions);
		
	}

	private SymmReducerFailTestOutcome compileSympanFiles() {
		
		Process gcc;
		try {
			String gccCommand = "gcc -O2 -o " + EXECUTABLE + " sympan.c group.c " +
					(Config.getBooleanOption(BooleanOption.PARALLELISE) ? "parallel_symmetry_pthreads.c " : "")
					+ "-DSAFETY -DNOREDUCE " + compilerDirectives;
			
			System.err.println(gccCommand);
			gcc = Runtime.getRuntime().exec(gccCommand);
		} catch (IOException e1) {
			return SymmReducerFailTestOutcome.GCCCompilationIOError;
		}

		ErrorStreamHandler errorHandler = new ErrorStreamHandler(gcc, false);
		errorHandler.start();
		
		try {
			gcc.waitFor();
		} catch (InterruptedException e) {
			return SymmReducerFailTestOutcome.GCCCompilationInterrupted;
		}
		
		if(0 != gcc.exitValue()) {
			return SymmReducerFailTestOutcome.GCCCompilationFailure;
		}

		return null; // Compilation was successful

	}

}
