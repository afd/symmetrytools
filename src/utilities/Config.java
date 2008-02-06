package src.utilities;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.StringTokenizer;

public class Config {

	public static final String VERSION = "2.0";
	public static String SAUCY = null;
	public static String GAP = null;
	public static String TEMP_FILES = null;
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
	public static boolean SIEVE = false;
	public static boolean OPENMP = false;
	public static int NO_CORES = 0; /* If this is 0, an iteratorclass is used for splitting
										If > 0 then explicit loops are generated */
	public static boolean PTHREADS = false;
	
	public static boolean isOSWindows() {
		return System.getProperty("os.name").length()>="Windows".length() && System.getProperty("os.name").substring(0,7).equals("Windows");
	}
	
	public static void readConfigFile(String filename) {
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

			if(TEMP_FILES==null) {
				System.out.println("No temporary directory specified.");
			}

			if(GAP==null || SAUCY==null ||COMMON==null || TEMP_FILES==null) {
				System.exit(1);
			}
			
		} catch (FileNotFoundException e) {
			configurationError();
		} catch (IOException e) {
			configurationError();
		}
	
	}

	private static void configurationError() {
		System.out.println("Error opening configuration file \"config.txt\", which should be located in the directory from which you run TopSPIN.");
		System.exit(0);
	}

	private static boolean timeboundset = false;
	private static boolean conjugatesset = false;
	private static boolean transpositionsset = false;
	private static boolean profileset = false;
	private static boolean strategyset = false;
	private static boolean stabiliserchainset = false;
	private static boolean sieveset = false;
	private static boolean openmpset = false;
	private static boolean pthreadsset = false;
	private static boolean coresset = false;

	private static void processConfigurationLine(String line, int n) {
		try {
			StringTokenizer strtok = new StringTokenizer(line,"=");
			if(strtok.countTokens()!=2) {
				throw new Exception();
			} else {
				String name = strtok.nextToken().toLowerCase();
				String value = strtok.nextToken();
			
				if(name.equals("gap") && GAP==null) {
					GAP = value;
				} else if(name.equals("saucy") && SAUCY==null) {
					SAUCY = value;
				} else if(name.equals("tempfiles") && TEMP_FILES==null) {
					TEMP_FILES = value;
				} else if(name.equals("common") && COMMON==null) {
					COMMON = value;
				} else if(name.equals("timebound") && !timeboundset) {
					timeboundset = true;
					TIME_BOUND = Integer.parseInt(value);
				} else if(name.equals("conjugates") && !conjugatesset) {
					conjugatesset = true;
					NO_CONJUGATES = Integer.parseInt(value);
				} else if(name.equals("symmetryfile") && AUTOS_FILE==null) {
					AUTOS_FILE = value;
					AUTOMATIC_DETECTION = false;
				} else if(name.equals("transpositions") && !transpositionsset) {
					transpositionsset = true;
					USE_TRANSPOSITIONS = Boolean.parseBoolean(value.toLowerCase());
				} else if(name.equals("stabiliserchain") && !stabiliserchainset) {
					stabiliserchainset = true;
					USE_STABILISER_CHAIN = Boolean.parseBoolean(value.toLowerCase());
				} else if(name.equals("profile") && !profileset) {
					profileset = true;
					PROFILE = Boolean.parseBoolean(value.toLowerCase());
				} else if(name.equals("strategy") && !strategyset) {
					strategyset = true;
					REDUCTION_STRATEGY = Strategy.valueOf(value.toUpperCase());
					if(REDUCTION_STRATEGY==null) {
						System.out.println("Unknown reduction strategy -- defaulting to " + Strategy.FAST);
						REDUCTION_STRATEGY = Strategy.FAST;
					}
				} else if(name.equals("sieve") && !sieveset) {
					sieveset = true;
					SIEVE = Boolean.parseBoolean(value.toUpperCase());
				} else if(name.equals("openmp") && !openmpset) {
					openmpset = true;
					OPENMP = Boolean.parseBoolean(value.toUpperCase());
				} else if(name.equals("pthreads") && !pthreadsset) {
					pthreadsset = true;
					PTHREADS = Boolean.parseBoolean(value.toUpperCase());
				} else if(name.equals("cores") && !coresset) {
					coresset = true;
					NO_CORES = Integer.parseInt(value);
				} else if(name.equals("quiet")) {
					ProgressPrinter.QUIET_MODE = Boolean.parseBoolean(value);
				} else {
					System.out.println("Line " + n + " of configuration file redefines a configuration item, or refers to an item which does not exist.");
				}
			}
		} catch(Exception e) {
			System.out.println("Line " + n + " of configuration file badly formed.");
		}
	}
}
