package src.utilities;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class Config {

	public static Map<Integer, Location> locations = new HashMap<Integer, Location>();
	
	public static boolean isOSWindows() {
		return System.getProperty("os.name").length()>="Windows".length() && System.getProperty("os.name").substring(0,7).equals("Windows");
	}
	
	
	
	public static void readConfigFile(String filename, boolean resetConfigurationOptions, boolean setDefaultConfigurationOptions) throws BadConfigurationFileException, AbsentConfigurationFileException {

		if(resetConfigurationOptions) {
			resetConfiguration();
		}

		try {
			BufferedReader br = new BufferedReader(new FileReader(filename));
			String line;
			int n=0;
			while((line=br.readLine())!=null) {
				processConfigurationLine(line,++n);
			}

			if(setDefaultConfigurationOptions) {
				setUnspecifiedOptionsToDefaultValues();
				
				if(null == getStringOption(StringOption.GAP)) {
					System.out.println("No configuration specified for GAP.");
				}
	
				if(null == getStringOption(StringOption.SAUCY)) {
					System.out.println("No configuration specified for saucy.");
				}
	
				if(null == getStringOption(StringOption.COMMON)) {
					System.out.println("No common directory specified.");
				}
					
				if(mandatoryOptionNotSet()) {
					if(TESTING_IN_PROGRESS) {
						throw new BadConfigurationFileException();
					}
					System.exit(1);
				}
	
				checkCommonDirectoryExists();
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


	private static void checkCommonDirectoryExists() throws BadConfigurationFileException {

		File commonDirectory = new File(getStringOption(StringOption.COMMON));
		if(!commonDirectory.exists()) {
			System.out.println(commonDirectory + " has been specified as the Common directory, but this directory does not exist.");
			if(TESTING_IN_PROGRESS) {
				throw new BadConfigurationFileException();
			}
			System.exit(1);
		}
		
		if(!commonDirectory.isDirectory()) {
			System.out.println(commonDirectory + " has been specified as the Common directory.  This location exists, but is not a directory.");
			if(TESTING_IN_PROGRESS) {
				throw new BadConfigurationFileException();
			}
			System.exit(1);
		}
		
		
	}



	public static void setUnspecifiedOptionsToDefaultValues() {
		for(StringOption option : stringOptions.keySet()) {
			if(null == stringOptions.get(option).getValue()) {
				stringOptions.get(option).setToDefaultValue();
			}
		}
		for(BooleanOption option : booleanOptions.keySet()) {
			if(null == booleanOptions.get(option).getValue()) {
				booleanOptions.get(option).setToDefaultValue();
			}
		}
		for(IntegerOption option : integerOptions.keySet()) {
			if(null == integerOptions.get(option).getValue()) {
				integerOptions.get(option).setToDefaultValue();
			}
		}
		for(StrategyOption option : strategyOptions.keySet()) {
			if(null == strategyOptions.get(option).getValue()) {
				strategyOptions.get(option).setToDefaultValue();
			}
		}
		
	}



	public static Strategy strategy() {
		return getStrategyOption(StrategyOption.STRATEGY);
	}



	private static boolean mandatoryOptionNotSet() {
		return (null==getStringOption(StringOption.GAP)) || (null==getStringOption(StringOption.SAUCY)) || (null==getStringOption(StringOption.COMMON));
	}

	private static void setIntegerOption(IntegerOption key, int value) {
		integerOptions.get(key).setValue(value);
	}
	
	public static void setBooleanOption(BooleanOption key, boolean value) {
		booleanOptions.get(key).setValue(value);
	}

	private static void setStringOption(StringOption key, String value) {
		stringOptions.get(key).setValue(value);
	}

	private static void setStrategyOption(StrategyOption key, Strategy value) {
		strategyOptions.get(key).setValue(value);
	}

	public static void setCommandLineSwitch(CommandLineSwitch flag) {
		// Set boolean switch - it is on or off, there is no data value.
		commandLineSwitchesCurrentlySet.put(flag, null);
	}

	private static void setCommandLineSwitchWithValue(CommandLineSwitch sw,
			String value) {
		commandLineSwitchesCurrentlySet.put(sw, value);
	}
	
	public static int getIntegerOption(IntegerOption key) {
		return integerOptions.get(key).getValue();
	}
	
	public static boolean getBooleanOption(BooleanOption key) {
		return booleanOptions.get(key).getValue();
	}

	public static String getStringOption(StringOption key) {
		return stringOptions.get(key).getValue();
	}

	public static Strategy getStrategyOption(StrategyOption key) {
		return strategyOptions.get(key).getValue();
	}

	public static boolean commandLineSwitchIsSet(CommandLineSwitch flag) {
		return (null != flag) && commandLineSwitchesCurrentlySet.containsKey(flag);
	}

	public static String getCommandLineSwitchValue(CommandLineSwitch sw) {
		return commandLineSwitchesCurrentlySet.get(sw);
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
		
		String name = null;
		
		try {
			final int indexOfEquals = line.indexOf('=');
			if(indexOfEquals==-1) {
				System.out.println("Ignoring line " + lineNumber + " of configuration file - it does not have the form option=value.");
				return;
			}
			name = StringHelper.trimWhitespace(line.substring(0, indexOfEquals)).toUpperCase();
			final String value = StringHelper.trimWhitespace(line.substring(indexOfEquals + 1));

			if(!(processStringOption(name, value) || processBooleanOption(name, value, lineNumber) || 
					processIntegerOption(name, value, lineNumber) || processStrategyOption(name, value, lineNumber))) {
				System.out.println("Unknown config file option '" + name + "' ignored at line " + lineNumber + " of config.txt.");
			}

		} catch(ConfigurationOptionAlreadyDefinedException e) {
			assert(null != name);
			System.out.println("Ignoring redefinition of \"" + name + "\" at line " + lineNumber + " of config.txt.");
		}

	}




	private static boolean processBooleanOption(String name, String value, int lineNumber) throws ConfigurationOptionAlreadyDefinedException {
		try {
			BooleanOption option = BooleanOption.valueOf(name);
			if(null != option) {
				if(null != booleanOptions.get(option).getValue()) {
					throw new ConfigurationOptionAlreadyDefinedException();
				}
				setBooleanOption(option, safelyParseBooleanOption(value, lineNumber));
				return true;
			}
			return false;
		} catch(IllegalArgumentException e) {
			return false;
		}
	}

	private static boolean processStringOption(String name, String value) throws ConfigurationOptionAlreadyDefinedException {
		try {
			StringOption option = StringOption.valueOf(name);
			if(null != option) {
				if(null != stringOptions.get(option).getValue()) {
					throw new ConfigurationOptionAlreadyDefinedException();
				}
				setStringOption(option, value);
				return true;
			}
			return false;
		} catch(IllegalArgumentException e) {
			return false;
		}
	}

	private static boolean processIntegerOption(String name, String value, int lineNumber) throws ConfigurationOptionAlreadyDefinedException {
		try {
			IntegerOption option = IntegerOption.valueOf(name);
			if(null != option) {
				if(null != integerOptions.get(option).getValue()) {
					throw new ConfigurationOptionAlreadyDefinedException();
				}
				setIntegerOption(option, safelyParseIntegerOption(value, lineNumber));
				return true;
			}
			return false;
		} catch(IllegalArgumentException e) {
			return false;
		}
	}

	private static boolean processStrategyOption(String name, String value, int lineNumber) throws ConfigurationOptionAlreadyDefinedException {
		try {
			StrategyOption option = StrategyOption.valueOf(name);
			if(null != option) {
				if(null != strategyOptions.get(option).getValue()) {
					throw new ConfigurationOptionAlreadyDefinedException();
				}
				setStrategyOption(option, safelyParseStrategyOption(value, lineNumber));
				return true;
			}
			return false;
		} catch(IllegalArgumentException e) {
			return false;
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


	public static void printConfiguration() {
		ProgressPrinter.println("Configuration settings:");
		ProgressPrinter.println("    Symmetry detection method: " + (automaticDetection()?"static channel diagram analysis":"manual"));

		if(!automaticDetection()) {
			ProgressPrinter.println("    Generators given in: " + getStringOption(StringOption.SYMMETRYFILE));
		} else {
			ProgressPrinter.println("    Using " + getIntegerOption(IntegerOption.CONJUGATES) + " random conjugate" + (getIntegerOption(IntegerOption.CONJUGATES)==1?"":"s"));
			ProgressPrinter.println("    Timeout for finding largest valid subgroup: " + getIntegerOption(IntegerOption.TIMEBOUND) + " seconds");
		}
		ProgressPrinter.println("    Reduction strategy: " + strategy());
		ProgressPrinter.println("    Using transpositions to represent permutations: " + getBooleanOption(BooleanOption.TRANSPOSITIONS));
		ProgressPrinter.println("    Using stabiliser chain for enumeration: " + getBooleanOption(BooleanOption.STABILISERCHAIN));
		ProgressPrinter.println("    Using vectorisation: " + getBooleanOption(BooleanOption.VECTORISE));
	}



	private static boolean automaticDetection() {
		return (null==getStringOption(StringOption.SYMMETRYFILE));
	}
	
	
	private static Map<BooleanOption, ConfigurationOptionEntry<Boolean>> booleanOptions;
	private static Map<StringOption, ConfigurationOptionEntry<String>> stringOptions;
	private static Map<IntegerOption, ConfigurationOptionEntry<Integer>> integerOptions;
	private static Map<StrategyOption, ConfigurationOptionEntry<Strategy>> strategyOptions;
	private static Map<CommandLineSwitch, String> commandLineSwitchDescriptions;
	
	private static Map<CommandLineSwitch, String> commandLineSwitchesCurrentlySet;
	public static String TOOL_NAME = "TopSPIN";
	
	public static void resetConfiguration() {

		booleanOptions = new HashMap<BooleanOption, ConfigurationOptionEntry<Boolean>>();
		stringOptions = new HashMap<StringOption, ConfigurationOptionEntry<String>>();
		integerOptions = new HashMap<IntegerOption, ConfigurationOptionEntry<Integer>>();
		strategyOptions = new HashMap<StrategyOption, ConfigurationOptionEntry<Strategy>>();
		commandLineSwitchDescriptions = new HashMap<CommandLineSwitch, String>();
		
		newStringOption(StringOption.SAUCY, null, "Config file option - path to the 'saucy' program.  Option must be set by user.");
		newStringOption(StringOption.COMMON, null, "Config file option - path to the 'Common' directory.  Option must be set by user.");
		newStringOption(StringOption.GAP, null, "Config file option - path to the 'gap' program.  Option must be set by user.");
		newStringOption(StringOption.TARGET, null, "Config file option - target to use for vector and parallel symmetry reduction.  Options are: PC, CELL, POWERPC.");
		newStringOption(StringOption.SYMMETRYFILE, null, "Config file option - path to the file containing symmetry group generators.  Only set this option if you want to disable automatic symmetry detection in favour of manual specification of symmetry.");
		newStringOption(StringOption.PREPROCESSOR_DIRECTIVES, null, "Config file option - directives that will be passed to the C preprocessor and to Spin - typically -D options.");

		newBooleanOption(BooleanOption.TRANSPOSITIONS, true, "Config file option - apply group elements as transpositions?");
		newBooleanOption(BooleanOption.STABILISERCHAIN, true, "Config file option - use stabiliser chain for enumeration?");
		newBooleanOption(BooleanOption.PROFILE, false, "Config file option - profile the performance of TopSPIN?");
		newBooleanOption(BooleanOption.VECTORISE, false, "Config file option - use vector SIMD instructions for symmetry reduction?");
		newBooleanOption(BooleanOption.VERBOSE, false, "Config file option - display progress of TopSPIN in detail?");
		newBooleanOption(BooleanOption.PARALLELISE, false, "Config file option - parallelise symmetry reduction using pthreads?");
		newBooleanOption(BooleanOption.QUIET, false, "Config file option - suppress non-vital output?");

		newIntegerOption(IntegerOption.TIMEBOUND, 0, "Config file option - specify time bound, in seconds, on coset search for largest valid subgroup.  Value of 0 means no bound.");
		newIntegerOption(IntegerOption.CONJUGATES, 0, "Config file optoin - number of random conjugates to use when finding largest valid subgroup.");
		newIntegerOption(IntegerOption.CORES, 1, "Config file option - number of cores available for parallel symmetry reduction.");
		newIntegerOption(IntegerOption.EXPLAIN, 0, "Config file option - number of invalid symmetries for which explanations should be produced.");

		newStrategyOption(StrategyOption.STRATEGY, Strategy.FAST, "Config file option - strategy to use for symmetry reduction.  Options are: " + strategyNames() + ".");

		commandLineSwitchDescriptions.put(CommandLineSwitch.CHECK, "Command line switch: apply this switch to only type-check input specification.");
		commandLineSwitchDescriptions.put(CommandLineSwitch.DETECT, "Command line switch: apply this switch to detect symmetry for input specification, but not apply symmetry reduction.");
		commandLineSwitchDescriptions.put(CommandLineSwitch.STRICTARRAYINDEXING, "Command line switch: disallow arrays to be indexed by expressions of numeric types larger than 'byte'.  With this option, attempts to index arrays using 'short' or 'int' expressions will be disallowed.");
		commandLineSwitchDescriptions.put(CommandLineSwitch.STRICTASSIGNMENT, "Command line switch: disallow assignments from larger to smaller numeric types, since such assignments may result in overflow.  With this option, e.g. assignment of an 'int' variable to a 'byte' variable will be disallowed.");
		commandLineSwitchDescriptions.put(CommandLineSwitch.CHANNELREDUNDANCY, "Command line switch: use Etch to erase user-specified channel initialisers, and compute potentially more efficient types for channels.");
		commandLineSwitchDescriptions.put(CommandLineSwitch.CPP, "Specify path to C preprocessor utility.  This can be necessary e.g. if you are using Windows with Cygwin, and cpp.exe is a symbolic link - currently it is necessary to supply the full path to the symbolic link target, in Windows form.");
		
	}

	private static String strategyNames() {
		String result = "";
		for(int i=0; i<Strategy.values().length; i++) {
			result += Strategy.values()[i].toString().toLowerCase();
			if(i<Strategy.values().length-1) {
				result += ", ";
			}
		}
		return result;
	}



	private static void newIntegerOption(IntegerOption key, Integer defaultValue, String helpMessage) {
		integerOptions.put(key, new ConfigurationOptionEntry<Integer>(defaultValue, helpMessage));
	}

	private static void newStringOption(StringOption key, String defaultValue, String helpMessage) {
		stringOptions.put(key, new ConfigurationOptionEntry<String>(defaultValue, helpMessage));
	}

	private static void newBooleanOption(BooleanOption key, Boolean defaultValue, String helpMessage) {
		booleanOptions.put(key, new ConfigurationOptionEntry<Boolean>(defaultValue, helpMessage));
	}

	private static void newStrategyOption(StrategyOption key, Strategy defaultValue, String helpMessage) {
		strategyOptions.put(key, new ConfigurationOptionEntry<Strategy>(defaultValue, helpMessage));
	}

	public static boolean profiling() {
		return getBooleanOption(BooleanOption.PROFILE);
	}

	public static void initialiseCommandLineSwitches() {
		commandLineSwitchesCurrentlySet = new HashMap<CommandLineSwitch, String>();
	}


	public static int processCommandLineSwitches(String[] args) {
		int currentArg = 0;
		
		while(currentArg < args.length) {
			if(processCommandLineSwitch(args[currentArg].toUpperCase())) {
				currentArg++;
			} else if((currentArg < args.length - 1) && processCommandLineSwitchWithValue(args[currentArg].toUpperCase(), args[currentArg+1])) {
				currentArg += 2;
			} else {
				break;
			}
		}

		return currentArg;
	}


	private static boolean processCommandLineSwitchWithValue(String arg,
			String value) {

		if(arg.length()<1 || arg.charAt(0) != '-') {
			return false;
		}

		String argName = arg.substring(1);

		if(argName.equals(CommandLineSwitch.CPP.toString())) {
			if(Config.commandLineSwitchIsSet(CommandLineSwitch.CPP)) {
				System.out.println("Warning: duplicate command line switch " + CommandLineSwitch.CPP + ".");
			} else {
				Config.setCommandLineSwitchWithValue(CommandLineSwitch.CPP, value);
			}
			return true;
		}
		return false;
		
		
		
	}




	private static boolean processCommandLineSwitch(String arg) {
		
		if(arg.length()<1 || arg.charAt(0) != '-') {
			return false;
		}
		
		String argName = arg.substring(1);
		
		return processSwitchVariant(argName, CommandLineSwitch.CHECK, CommandLineSwitch.DETECT)
		|| processSwitchVariant(argName, CommandLineSwitch.DETECT, CommandLineSwitch.CHECK)
		|| processSwitchVariant(argName, CommandLineSwitch.STRICTARRAYINDEXING, null)
		|| processSwitchVariant(argName, CommandLineSwitch.STRICTASSIGNMENT, null)
		|| processSwitchVariant(argName, CommandLineSwitch.CHANNELREDUNDANCY, null);

	}

	private static boolean processSwitchVariant(String arg, CommandLineSwitch commandLineSwitch, CommandLineSwitch otherSwitch) {
		if(arg.equals(commandLineSwitch.toString())) {
			if(Config.commandLineSwitchIsSet(commandLineSwitch)) {
				System.out.println("Warning: duplicate command line switch " + commandLineSwitch + ".");
			} else if(Config.commandLineSwitchIsSet(otherSwitch)) {
				System.out.println("Warning: " + commandLineSwitch + " switch has been ignored as it is specified after " + otherSwitch + " switch.");
			} else {
				Config.setCommandLineSwitch(commandLineSwitch);
			}
			return true;
		}
		return false;
	}
	
	
	/* Including 'etchMode' as a parameter is not a great way to handle this. */
	public static void showHelpForConfigurationOption(String option, boolean etchMode) {
		
		option = option.length() > 0 && option.charAt(0) == '-' ? option.substring(1) : option;

		try {
			System.out.println(booleanOptions.get(BooleanOption.valueOf(option.toUpperCase())).helpString(option, "boolean"));
		} catch(IllegalArgumentException notBooleanOption) {
			try {
				System.out.println(stringOptions.get(StringOption.valueOf(option.toUpperCase())).helpString(option, "String"));
			} catch(IllegalArgumentException notStringOption) {
				try {
					System.out.println(integerOptions.get(IntegerOption.valueOf(option.toUpperCase())).helpString(option, "integer"));
				} catch(IllegalArgumentException notIntegerOption) {
					try {					
						System.out.println(strategyOptions.get(StrategyOption.valueOf(option.toUpperCase())).helpString(option, "string"));
					} catch(IllegalArgumentException notStrategyOption) {
						try {
							CommandLineSwitch commandLineSwitch = CommandLineSwitch.valueOf(option.toUpperCase());
							if((etchMode && ((CommandLineSwitch.CHECK == commandLineSwitch) || (CommandLineSwitch.DETECT == commandLineSwitch)))
									||
							   (!etchMode && (CommandLineSwitch.CHANNELREDUNDANCY == commandLineSwitch))) {
								throw new IllegalArgumentException();
							}
							System.out.println(commandLineSwitchDescriptions.get(commandLineSwitch));
						} catch(IllegalArgumentException notCommandLineSwitch) {
							System.out.println("Error: Unknown config file option or command-line switch \"" + option + "\"");
						}
					}
				}
			}
		}
	}


	public static boolean inQuietMode() {
		return Config.getBooleanOption(BooleanOption.QUIET);
	}

	public static boolean inVerboseMode() {
		return getBooleanOption(BooleanOption.VERBOSE);
	}
}
