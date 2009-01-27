package src.symmextractor;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PushbackReader;
import java.io.StringReader;
import java.util.HashSet;
import java.util.Set;

import src.etch.checker.Check;
import src.etch.checker.Checker;
import src.etch.typeinference.Substituter;
import src.group.Group;
import src.group.Permutation;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.utilities.CommandLineSwitch;
import src.utilities.CommunicatingProcess;
import src.utilities.Config;
import src.utilities.ErrorStreamHandler;
import src.utilities.IntegerOption;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;
import src.utilities.StringOption;


public class SymmExtractor extends Check {

	protected Process gap;
	protected BufferedReader gapReader;
	protected BufferedWriter gapWriter;
	private Group autSCD;
	private Group largestValidSubgroup;
	private boolean requiredCosetSearch = false;
	private long sizeOfLargestValidSubgroup = -1;
	private boolean isWellTyped;
	public boolean obeysSymmetryRestrictions;
	
	public StaticChannelDiagramExtractor makeStaticChannelDiagramExtractor() {
		return new StaticChannelDiagramExtractor();
	}
	
	public SymmExtractor(String sourceName) throws IOException, ParserException, LexerException {
		super(sourceName);
	}

	public boolean isWellTyped() {
		return isWellTyped;
	}
	
	public StaticChannelDiagramExtractor extract() throws IOException {

		if(Config.profiling()) { Profile.EXTRACT_START = System.currentTimeMillis(); }
		
		isWellTyped = typecheck(true);
		
		if(isWellTyped) {
			if(Config.inVerboseMode()) {
				ProgressPrinter.printSeparator();
				ProgressPrinter.println("Reparsing source without inlines");
			}
			reparseSourceWithoutInlines();

			StaticChannelDiagramExtractor extractor	= makeStaticChannelDiagramExtractor();
			
			theAST.apply(extractor);

			obeysSymmetryRestrictions = checkSymmetryResrictionsAreObeyed(extractor);
				
			if(obeysSymmetryRestrictions) {
			
				Substituter substituter = extractor.unify();
				applyTypeSubstitutions(extractor, substituter);
				if(Config.profiling()) { Profile.EXTRACT_END = System.currentTimeMillis(); }
	
				if(Config.profiling()) { Profile.SAUCY_START = System.currentTimeMillis(); }

				if(Config.inVerboseMode()) {
					ProgressPrinter.printSeparator();
				}
				
				computeStaticChannelDiagramAutomorphisms(extractor);
				if(Config.profiling()) { Profile.SAUCY_END = System.currentTimeMillis(); }

				if(Config.inVerboseMode()) {
					ProgressPrinter.println("Saucy computed the following generators for Aut(SCD(P)):");
					ProgressPrinter.println("   Aut(SCD(P)) = " + autSCD);
				}
	
				if(Config.profiling()) { Profile.LARGEST_VALID_START = System.currentTimeMillis(); }
				computeLargestValidSubgroup(extractor);
	
				if(Config.inVerboseMode()) {
					ProgressPrinter.printSeparator();
				} else {
					ProgressPrinter.print("\n");
				}

				ProgressPrinter.println("The group:");
				ProgressPrinter.println("   G = " + largestValidSubgroup);
				ProgressPrinter.println("is a valid group for symmetry reduction.");

				if(Config.inVerboseMode()) {
					ProgressPrinter.printSeparator();
				} else {
					ProgressPrinter.print("\n");
				}
	
				return extractor;
			}
		}
		if(Config.profiling()) { Profile.EXTRACT_END = System.currentTimeMillis(); }
		return null;
	}

	private boolean checkSymmetryResrictionsAreObeyed(StaticChannelDiagramExtractor extractor) {
		if(extractor.getErrorTable().hasErrors()) {
			if(!Config.inQuietMode()) {
				System.out.println(extractor.getErrorTable().output("while processing " + sourceName));
			}
			return false;
		}
		
		return true;

	}
	
	protected void reparseSourceWithoutInlines() {
		InlineReplacer inlineReplacer = new InlineReplacer();
		theAST.apply(inlineReplacer);
		String inlinedSourceProgram = inlineReplacer.getInlinedProgram();
		
		parseInputString(inlinedSourceProgram);
	}

	private void computeLargestValidSubgroup(StaticChannelDiagramExtractor extractor)
			throws IOException {

		boolean someGeneratorsInvalid = false;

		if(Config.inVerboseMode()) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Computing valid generators:");
		}
		
		Set<Permutation> safeGenerators = new HashSet<Permutation>();
				
		for(Permutation alpha : autSCD.getGenerators()) {
			if (alpha.isSafeFor(theAST, extractor)) {
				if(Config.inVerboseMode()) {
					ProgressPrinter.println("    " + alpha + " : valid");
				}
				safeGenerators.add(alpha);
			} else {
				if(Config.inVerboseMode()) {
					ProgressPrinter.println("    " + alpha + " : not valid");
				}
				someGeneratorsInvalid = true;
			}
		}
		Group baseGroup = new Group(safeGenerators);

		if(someGeneratorsInvalid) {
			
			requiredCosetSearch  = true;
			
			startGAP();

			// Send Aut(SCD) = G to GAP, and H, the initial valid subgroup.
			gapWriter.write("G := " + autSCD.gapGenerators(extractor) + ";\n");
			gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");


			if(Config.profiling()) {
				gapWriter.write("Size(G);\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				ProgressPrinter.println("Size of Aut(SCD(P)): " + gapReader.readLine());
				ProgressPrinter.println("Size of base group: " + gapReader.readLine());
			}
			
			
			if(Config.getIntegerOption(IntegerOption.CONJUGATES)>0) {
				enlargeBaseGroupWithRandomConjugates(baseGroup.noGenerators(), extractor);
			}

			ProgressPrinter.println("Finding largest valid subgroup");
			
			gapWriter.write("C := RightTransversal(G,H);;\n");
			gapWriter.write("Size(C);\n");
			gapWriter.flush();

			int noCosets = Integer.parseInt(gapReader.readLine());
			
			if(Config.inVerboseMode()) {
				ProgressPrinter.println("No cosets: " + noCosets);
			}

			int j = 2;
			long initialTime = System.currentTimeMillis();
			while (j <= noCosets && (Config.getIntegerOption(IntegerOption.TIMEBOUND)==0 || 
					(System.currentTimeMillis()-initialTime < Config.getIntegerOption(IntegerOption.TIMEBOUND)))) {
				gapWriter.write("C[" + j + "];\n");
				gapWriter.flush();

				Permutation nextRepresentative = getPerm(extractor);

				if (nextRepresentative.isSafeFor(theAST, extractor)) {
					ProgressPrinter.println("    " + nextRepresentative + " : valid");
					addRepresentativeToGenerators(j);
					int newNoCosets = recomputeCosetRepresentatives(noCosets,j);
					if(newNoCosets!=-1) {
						noCosets = newNoCosets;
						ProgressPrinter.println("No cosets: " + noCosets);
						j = 2;
					} else {
						ProgressPrinter.println("No cosets: " + (noCosets-j));
						j++;
					}
				} else {
					j++;
				}
			}
			largestValidSubgroup = getFinalGroupFromGAP(extractor);

			if(Config.TESTING_IN_PROGRESS) {
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
			}
	
			if(Config.profiling()) {
				Profile.LARGEST_VALID_END = System.currentTimeMillis();
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				ProgressPrinter.println("Size of largest valid subgroup: " + gapReader.readLine());
			}
		} else {
			largestValidSubgroup = baseGroup;

			if(Config.commandLineSwitchIsSet(CommandLineSwitch.DETECT) && Config.TESTING_IN_PROGRESS) {
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
			}
			
			
			if(!Config.commandLineSwitchIsSet(CommandLineSwitch.DETECT)) {
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");

				if(Config.TESTING_IN_PROGRESS) {
					gapWriter.write("Size(H);\n");
					gapWriter.flush();
					sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
				}
			
			} else if(Config.profiling()) {
				Profile.LARGEST_VALID_END = System.currentTimeMillis();
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				ProgressPrinter.println("Size of Aut(SCD(P)): " + gapReader.readLine());
			}
		}
	}

	public void destroyGAP() throws IOException, InterruptedException {
		if(gap==null) {
			return;
		}
		gapWriter.write("quit;\n");
		gapWriter.flush();
		gap.waitFor();
		gapReader.close();
		gapWriter.close();
		gap.destroy();
	}

	private Group getFinalGroupFromGAP(StaticChannelDiagramExtractor extractor) throws IOException {
		gapWriter.write("Size(GeneratorsOfGroup(H));\n");
		gapWriter.write("Print(JoinStringsWithSeparator(GeneratorsOfGroup(H),\"\\n\"),\"\\n\");\n");
		gapWriter.flush();

		int noGenerators = Integer.parseInt(gapReader.readLine());

		Set<Permutation> generators = new HashSet<Permutation>();
		for(int i=0; i<noGenerators; i++) {
			generators.add(getPerm(extractor));
		}

		return new Group(generators);
	}

	private int recomputeCosetRepresentatives(int noCosets, int j) throws IOException {
		gapWriter.write("D := RightTransversal(G,H);;\n");
		gapWriter.write("Size(D);\n");
		gapWriter.flush();
		int sizeOfNewTransversal = Integer.parseInt(gapReader.readLine());
		if (sizeOfNewTransversal < noCosets-j) {
			gapWriter.write("C := D;;\n");
			gapWriter.flush();
			return sizeOfNewTransversal;
		}
		return -1;
	}

	private Permutation getPerm(StaticChannelDiagramExtractor extractor) throws IOException {
		String perm = gapReader.readLine();
		
		while (perm.charAt(perm.length() - 1) == ',' || perm.charAt(perm.length() - 1) == '\\') {
			if(perm.charAt(perm.length()-1)=='\\') {
				perm = perm.substring(0,perm.length()-1);
			}
			
			perm = perm + gapReader.readLine();

		}

		return new Permutation(perm,extractor,true);
	}

	private void addRepresentativeToGenerators(int representativePosition) throws IOException {
		gapWriter
				.write("H := Group(Concatenation(GeneratorsOfGroup(H),[C["
						+ representativePosition + "]]));;\n");
	}

	private void enlargeBaseGroupWithRandomConjugates(int noGenerators, StaticChannelDiagramExtractor extractor) throws IOException {

		for (int l = 1; l <= Config.getIntegerOption(IntegerOption.CONJUGATES); l++) {
			gapWriter.write("alpha := Random(G);;\n");
			for (int j = 1; j <= noGenerators; j++) {
				gapWriter.write("(alpha^-1) * (GeneratorsOfGroup(H)[" + j
						+ "]) * alpha;\n");
			}
			
			gapWriter.flush();
			
			for(int j = 1; j <= noGenerators; j++) {
				Permutation pe = getPerm(extractor);
				if (pe.isSafeFor(theAST, extractor)) {
					gapWriter.write("alpha := " + pe.gapRepresentation(extractor) + ";;\n");
					gapWriter.write("if (not (alpha in H)) then\n");
					gapWriter.write("H := Group(Concatenation(GeneratorsOfGroup(H),[alpha]));;\n");
					gapWriter.write("fi;;\n");
				}
			}
		}
		
	}

	private void computeStaticChannelDiagramAutomorphisms(
			StaticChannelDiagramExtractor extractor) {

		try {
			FileWriter fw = new FileWriter(Config.getStringOption(StringOption.COMMON)+"graph.saucy");
			fw.write(extractor.directedSaucyRepresentation());
			fw.close();
		} catch(FileNotFoundException e) {
			System.out.println("Error while trying to create file \"" + Config.getStringOption(StringOption.COMMON)+"graph.saucy\".  Make sure that the directory " + Config.getStringOption(StringOption.COMMON) + " exists, and that you have write permission.");
			System.exit(1);
		} catch (IOException e) {
			System.out.println("An error occurred while trying to create the file \"" + Config.getStringOption(StringOption.COMMON)+"graph.saucy\".");
			System.exit(1);
		}
		
		if(Config.inVerboseMode()) {
			ProgressPrinter.println("Computing the group Aut(C(P)) using directed saucy.");
		}
		String saucyGenerators = computeAutomorphismsOfDirectedGraph(Config.getStringOption(StringOption.COMMON)+"graph.saucy");
		
		autSCD = new Group(saucyGenerators, extractor);
	}

	private static String computeAutomorphismsOfDirectedGraph(String filename) {

		String result = "";
		
		String saucyString; 
		if(Config.isOSWindows()) {
			saucyString = Config.getStringOption(StringOption.SAUCY) + " -d \"" + filename + "\"";
		} else {
			saucyString = Config.getStringOption(StringOption.SAUCY) + " -d " + filename;
		}

		ProgressPrinter.println("\nLaunching saucy via the following command: " + saucyString + "\n");
		
		Process saucy = null;
		try {
			saucy = CommunicatingProcess.create(saucyString);
		} catch (IOException e) {
			System.out.println("Error launching saucy with command: " + saucyString);
			e.printStackTrace();
			System.exit(1);
		}

		ErrorStreamHandler errorHandler = new ErrorStreamHandler(saucy, "\nsaucy produced errors:\n======================",  "End of saucy errors", true);
		errorHandler.start();
		
		BufferedReader br = CommunicatingProcess.getReader(saucy);
		String temp;
		try {
			while ((temp = br.readLine()) != null) {
				result += temp + "\n";
			}
			br.close();
		} catch (IOException ioe) {
			ProgressPrinter.println("Error while getting output from saucy.");
		}
		

		if(result.equals("")) {
			System.out.println("The static channel diagram for the input specification has no non-trivial symmetry, so symmetry reduction cannot be applied.");
			System.out.println("If you are sure that symmetry *is* present in the static channel diagram then check that the saucy command executed above is the correct path to saucy.");
			System.out.println("* N.B. make sure you are using the version of saucy with digraph support, supplied with TopSPIN *");
			System.exit(0);
		}

		return result;

	}

	protected void applyTypeSubstitutions(Checker chk,
		Substituter substituter) {
		substituter.setTypeInformation(chk);
		theAST.apply(substituter);
	}

	private void parseInputString(String source) {
		Lexer scanner = new Lexer(new PushbackReader(new BufferedReader(new StringReader(source))));
		Parser parser = new Parser(scanner);
		try {
			theAST = parser.parse();
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
	}
	
	protected void startGAP() throws IOException {
		
		if(Config.profiling()) { Profile.GAP_LAUNCH_START = System.currentTimeMillis(); }

		String gapString;

		if(Config.isOSWindows()) {
			gapString = Config.getStringOption(StringOption.GAP) + " -L \"" + Config.getStringOption(StringOption.COMMON) + "gapworkspace\" -q";
		} else {
			gapString = Config.getStringOption(StringOption.GAP) + " -L " + Config.getStringOption(StringOption.COMMON) + "gapworkspace -q";
		}
		if(Config.inVerboseMode()) {
			ProgressPrinter.printSeparator();
		}
		ProgressPrinter.print("Starting GAP with command: " + gapString + "\n");

		gap = CommunicatingProcess.create(gapString);
		
		gapReader = CommunicatingProcess.getReader(gap);
		gapWriter = CommunicatingProcess.getWriter(gap);

		ErrorStreamHandler esh = new ErrorStreamHandler(gap, "\nGAP produced errors:\n====================",  "End of GAP errors", true);
		esh.start();
		
		gapWriter.write("0;\n");
		gapWriter.flush();

		if(Config.inVerboseMode()) {
			ProgressPrinter.println("Output produced by GAP at startup:");
		}
		String line = gapReader.readLine();
		while(!line.equals("0")) {
			
			if(Config.inVerboseMode()) {
				ProgressPrinter.println(line);
			}
			if(line.contains("Couldn't open saved workspace")) {
				ProgressPrinter.println("Error -- bad GAP workspace specified in configuration file.");
			}
			
			line = gapReader.readLine();
		}
		
		if(Config.profiling()) { Profile.GAP_LAUNCH_END = System.currentTimeMillis(); }

	}

	public void printGAPError() throws IOException {
		System.out.println((new BufferedReader(new InputStreamReader(gap.getErrorStream()))).readLine());
	}

	public long getSizeOfGroup() {
		return sizeOfLargestValidSubgroup;
	}

	public boolean requiredCosetSearch() {
		return requiredCosetSearch;
	}

}
