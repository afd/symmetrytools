package src.utilities;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.StringTokenizer;

import src.symmreducer.paralleltargets.CellParallelTarget;
import src.symmreducer.paralleltargets.ParallelTarget;
import src.symmreducer.paralleltargets.PthreadsParallelTarget;
import src.symmreducer.vectortargets.CellSPUVectorTarget;
import src.symmreducer.vectortargets.VectorTarget;
import src.symmreducer.vectortargets.DummyVectorTarget;
import src.symmreducer.vectortargets.PowerPCVectorTarget;

public class Config {

	public static final String VERSION = "2.0";
	public static String SAUCY = null;
	public static String GAP = null;
	public static String COMMON = null;
	public static int TIME_BOUND = 0;
	public static int NO_CONJUGATES = 0;
	public static boolean AUTOMATIC_DETECTION = true;
	public static String AUTOS_FILE = null;
	public static Strategy REDUCTION_STRATEGY = Strategy.FAST;
	public static boolean USE_TRANSPOSITIONS = true;
	public static boolean USE_STABILISER_CHAIN = true;
	public static boolean PROFILE = false;
	public static boolean DETECT_ONLY = false;
	public static boolean VECTORIZE_ID_SWAPPING = false;
	public static boolean VERBOSE = false;
	
	public static int NO_CORES = 1;
	
	public static boolean PARALLELISE = false;

	private static Map<String, Integer> previouslySetOptions = new HashMap<String,Integer>();

	public static VectorTarget vectorTarget;
	public static ParallelTarget parallelTarget;
	
	public static void resetConfiguration() {
		
		SAUCY = null;
		GAP = null;
		COMMON = null;
		TIME_BOUND = 0;
		NO_CONJUGATES = 0;
		AUTOMATIC_DETECTION = true;
		AUTOS_FILE = null;
		REDUCTION_STRATEGY = Strategy.FAST;
		USE_TRANSPOSITIONS = true;
		USE_STABILISER_CHAIN = true;
		PROFILE = false;
		DETECT_ONLY = false;
		VECTORIZE_ID_SWAPPING = false;
		NO_CORES = 1;
		PARALLELISE = false;
		VERBOSE = false;
		previouslySetOptions = new HashMap<String,Integer>();

	}
	
	
	public static boolean isOSWindows() {
		return System.getProperty("os.name").length()>="Windows".length() && System.getProperty("os.name").substring(0,7).equals("Windows");
	}
	
	
	
	public static void readConfigFile(String filename) throws BadConfigurationFileException, AbsentConfigurationFileException {
		vectorTarget = new DummyVectorTarget();

		try {
			BufferedReader br = new BufferedReader(new FileReader(filename));
			String line;
			int n=0;
			while((line=br.readLine())!=null) {
				processConfigurationLine(line,++n);
			}

			if(GAP==null) {
				System.out.println("No configuration specified for GAP.");
			}

			if(SAUCY==null) {
				System.out.println("No configuration specified for saucy.");
			}

			if(COMMON==null) {
				System.out.println("No common directory specified.");
			}

			if(VECTORIZE_ID_SWAPPING && !USE_TRANSPOSITIONS) {
				ProgressPrinter.println("Vectorisation can only be applied when transpositions are used.  Vectorisation has been turned off.");
				VECTORIZE_ID_SWAPPING = false;
			}

			if(VECTORIZE_ID_SWAPPING && REDUCTION_STRATEGY==Strategy.FLATTEN) {
				ProgressPrinter.println("Vectorisation is not compatible with the FLATTEN strategy.  Vectorisation has been turned off.");
				VECTORIZE_ID_SWAPPING = false;
			}			
			
			if(GAP==null || SAUCY==null ||COMMON==null) {
				if(TESTING_IN_PROGRESS) {
					throw new BadConfigurationFileException();
				}
				System.exit(1);
			}
			
		} catch (FileNotFoundException e) {
			if(TESTING_IN_PROGRESS) {
				throw new AbsentConfigurationFileException();
			}
			configurationError();
		} catch (IOException e) {
			if(TESTING_IN_PROGRESS) {
				throw new BadConfigurationFileException();
			}
			configurationError();
		}
	
	}

	private static void configurationError() {
		System.out.println("Error opening configuration file \"config.txt\", which should be located in the directory from which you run TopSPIN.");
		System.exit(0);
	}

	public static boolean TESTING_IN_PROGRESS = false;
	
	private static void processConfigurationLine(String line, int lineNumber) {
		if(StringHelper.isWhitespace(line)) {
			return;
		}
		
		try {
			StringTokenizer strtok = new StringTokenizer(line,"=");
			if(strtok.countTokens()!=2) {
				throw new Exception();
			} else {
				String name = StringHelper.trimWhitespace(strtok.nextToken().toLowerCase());
				String value = StringHelper.trimWhitespace(strtok.nextToken());

				if(previouslySetOptions.containsKey(name)) {
					System.out.println("Ignoring redefinition of \"" + name + "\" at line " + lineNumber + " of config.txt.");
				} else {

					previouslySetOptions.put(name, lineNumber);
					
					if(name.equals("gap")) {
						GAP = value;
					} else if(name.equals("saucy")) {
						SAUCY = value;
					} else if(name.equals("common")) {
						COMMON = value;
					} else if(name.equals("timebound")) {
						TIME_BOUND = safelyParseIntegerOption(value, lineNumber);
					} else if(name.equals("conjugates")) {
						NO_CONJUGATES = safelyParseIntegerOption(value, lineNumber);
					} else if(name.equals("symmetryfile")) {
						AUTOS_FILE = value;
						AUTOMATIC_DETECTION = false;
					} else if(name.equals("transpositions")) {
						USE_TRANSPOSITIONS = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("stabiliserchain")) {
						USE_STABILISER_CHAIN = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("profile")) {
						PROFILE = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("strategy")) {
						REDUCTION_STRATEGY = safelyParseStrategyOption(value, lineNumber);
					} else if(name.equals("parallelise")) {
						PARALLELISE = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("cores")) {
						NO_CORES = safelyParseIntegerOption(value, lineNumber);
					} else if(name.equals("quiet")) {
						ProgressPrinter.QUIET_MODE = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("verbose")) {
						ProgressPrinter.VERBOSE_MODE = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("vectorise")) {
						VECTORIZE_ID_SWAPPING = safelyParseBooleanOption(value, lineNumber);
					} else if(name.equals("target")) {
						String upperCaseValue = value.toUpperCase();
						if(upperCaseValue.equals("PC")) {
							vectorTarget = new DummyVectorTarget();
							parallelTarget = new PthreadsParallelTarget();
						} else if(upperCaseValue.equals("POWERPC")) {
							vectorTarget = new PowerPCVectorTarget();
							parallelTarget = new PthreadsParallelTarget();
						} else if(upperCaseValue.equals("CELL")) {
							vectorTarget = new CellSPUVectorTarget();
							parallelTarget = new CellParallelTarget();
						} else {
							System.out.println("Unknown target '" + value + "' at line " + lineNumber + " of config.txt.  Defaulting to PC target.");
						}
					} else {
						System.out.println("Unknown configuration option '" + name + "' ignored at line " + lineNumber + " of config.txt.");
					}
				}
			}
		} catch(Exception e) {
			System.out.println("Ignoring line " + lineNumber + " of configuration file - it does not have the form option=value.");
		}
	}

	/* Method to return an integer given a string.
	 * If the string does not correspond to an integer,
	 * 0 is returned.
	 */
	private static int safelyParseIntegerOption(final String value, final int lineNumber) {
		if(value.equals("")) {
			System.out.println("No integer specified on right hand side of '=' at line " + lineNumber + " of config.txt.  Defaulting to '0'.");
			return 0;
		}

		try {
			return Integer.parseInt(value);
		} catch (Exception e) {
			System.out.println("Badly formed integer value '" + value + "' interpreted as '0' at line " + lineNumber + " of config.txt.");
			return 0;
		}
	}

	private static Strategy safelyParseStrategyOption(final String value, final int lineNumber) {
		if(value.equals("")) {
			System.out.println("No strategy specified on right hand side of '=' at line " + lineNumber + " of config.txt.  Defaulting to 'FAST'.");
			return Strategy.FAST;
		}
		
		try {
			Strategy result = Strategy.valueOf(value.toUpperCase());
			if(result == null) {
				System.out.println("Badly formed strategy '" + value + "' interpreted as 'FAST' at line " + lineNumber + " of config.txt.");
				result = Strategy.FAST;
			}
			return result;
		} catch(IllegalArgumentException e) {
			System.out.println("Badly formed strategy '" + value + "' interpreted as 'FAST' at line " + lineNumber + " of config.txt.");
			return Strategy.FAST;
		}
	}

	/* Method to return a boolean given a case-insensitive string.
	 * If the string does not correspond to a boolean, 'false' is
	 * returned.
	 */
	private static boolean safelyParseBooleanOption(final String value, final int lineNumber) {
		if(value.equals("")) {
			System.out.println("No boolean specified on right hand side of '=' at line " + lineNumber + " of config.txt.  Defaulting to 'false'.");
			return false;
		}

		if(!(value.toLowerCase().equals("true") || value.toLowerCase().equals("false"))) {
			System.out.println("Badly formed boolean value '" + value + "' interpreted as 'false' at line " + lineNumber + " of config.txt.");
			return false;
		}
		return Boolean.parseBoolean(value.toLowerCase());
	}

	public static void printOptions() {

		System.out.println("");
		System.out.println("Configuration file options:");
		System.out.println("");
		System.out.println(" OPTION           PURPOSE                                                                 DEFAULT ");
		System.out.println(" ------           -------                                                                 ------- ");
		System.out.println("");
		System.out.println("  gap              Path: location of gap package                                          N/A - compulsory");
		System.out.println("  saucy            Path: location of saucy program                                        N/A - compulsory");
		System.out.println("  common           Path: location of 'Common' folder, part of TopSpin distribution        N/A - compulsory");
		System.out.println("");
		System.out.println("  transpositions   Boolean: apply group elements as transpositions?                       true");
		System.out.println("  stabiliserchain  Boolean: use stabiliser chain for enumeration?                         true");
		System.out.println("  conjugates       Integer: no. of random conjugates when finding largest valid subgroup  0");
		System.out.println("  timebound        Integer: max. seconds allowed for finding largest valid subgroup       0 => search indefinitely");
		System.out.println("  symmetryfile     Bypass symmetry detection by providing a file of group generators      No file specified");
		System.out.println("");
		System.out.println("  strategy         Symmetry reduction strategy.  Options are:                             FAST");
		System.out.println("                     FAST, ENUMERATE, HILLCLIMBING, SEGMENT,");
		System.out.println("                     FLATTEN, EXACTMARKERS, APPROXMARKERS");
		System.out.println("");
		System.out.println("  pthreads         Boolean: parallelise symmetry reduction using pthreads                 false");
		System.out.println("  cores            Integer: number of cores for parallel symmetry reduction               1");
		System.out.println("  vectorise        Boolean: use vector SIMD instructions for symmetry reduction           false");
		System.out.println("");
		System.out.println("  profile          Boolean: output profiling information?                                 false");
		System.out.println("  quiet            Boolean: run TopSpin in quiet mode                                     false");

		
		
	}

	public static void printConfiguration() {
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
		ProgressPrinter.println("    Using vectorisation: " + Config.VECTORIZE_ID_SWAPPING);
	}
}
