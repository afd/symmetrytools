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
import java.util.Iterator;
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
import src.utilities.CommunicatingProcess;
import src.utilities.Config;
import src.utilities.ErrorStreamHandler;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;


public class SymmExtractor extends Check {

	protected Process gap;
	protected BufferedReader gapReader;
	protected BufferedWriter gapWriter;
	private StaticChannelDiagramExtractor extractor;
	private Group autSCD;
	private Group largestValidSubgroup;
	private boolean requiredCosetSearch = false;
	private long sizeOfLargestValidSubgroup = -1;
	private boolean isWellTyped;
	public boolean obeysSymmetryRestrictions;
	
	public SymmExtractor(String sourceName) throws IOException, ParserException, LexerException {
		super(sourceName);
	}

	public boolean isWellTyped() {
		return isWellTyped;
	}
	
	public StaticChannelDiagramExtractor extract() throws IOException {

		if(Config.PROFILE) { Profile.EXTRACT_START = System.currentTimeMillis(); }
		extractor = new StaticChannelDiagramExtractor();
		
		isWellTyped = typecheck(true);
		
		if(isWellTyped) {
			ProgressPrinter.printSeparator();
			ProgressPrinter.println("Reparsing source without inlines");
			reparseSourceWithoutInlines();
			theAST.apply(extractor);

			obeysSymmetryRestrictions = checkSymmetryResrictionsAreObeyed(extractor);
				
			if(obeysSymmetryRestrictions) {
			
				Substituter substituter = extractor.unify();
				applyTypeSubstitutions(extractor, substituter);
				if(Config.PROFILE) { Profile.EXTRACT_END = System.currentTimeMillis(); }
	
				if(Config.PROFILE) { Profile.SAUCY_START = System.currentTimeMillis(); }
				ProgressPrinter.printSeparator();
				computeStaticChannelDiagramAutomorphisms(extractor);
				if(Config.PROFILE) { Profile.SAUCY_END = System.currentTimeMillis(); }
				
				ProgressPrinter.println("Saucy computed the following generators for Aut(SCD(P)):");
				ProgressPrinter.println("   Aut(SCD(P)) = " + autSCD);
	
				if(Config.PROFILE) { Profile.LARGEST_VALID_START = System.currentTimeMillis(); }
				computeLargestValidSubgroup();
	
				ProgressPrinter.printSeparator();
				ProgressPrinter.println("The group:");
				ProgressPrinter.println("   G = " + largestValidSubgroup);
				ProgressPrinter.println("is a valid group for symmetry reduction.");
				ProgressPrinter.printSeparator();
	
				return extractor;
			}
		}
		if(Config.PROFILE) { Profile.EXTRACT_END = System.currentTimeMillis(); }
		return null;
	}


	private boolean checkSymmetryResrictionsAreObeyed(StaticChannelDiagramExtractor extractor) {
		if(extractor.getErrorTable().hasErrors()) {
			if(!ProgressPrinter.QUIET_MODE) {
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

	private void computeLargestValidSubgroup()
			throws IOException {

		boolean someGeneratorsInvalid = false;
		ProgressPrinter.printSeparator();
		ProgressPrinter.println("Computing valid generators:");
		Set<Permutation> safeGenerators = new HashSet<Permutation>();
				
		for(Iterator<Permutation> i = autSCD.iterator(); i.hasNext();) {
			Permutation alpha = i.next();
			if (alpha.isSafeFor(theAST, extractor)) {
				ProgressPrinter.println("    " + alpha + " : valid");
				safeGenerators.add(alpha);
			} else {
				ProgressPrinter.println("    " + alpha + " : not valid");
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


			if(Config.PROFILE) {
				gapWriter.write("Size(G);\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				ProgressPrinter.println("Size of Aut(SCD(P)): " + gapReader.readLine());
				ProgressPrinter.println("Size of base group: " + gapReader.readLine());
			}
			
			
			if(Config.NO_CONJUGATES>0) {
				enlargeBaseGroupWithRandomConjugates(baseGroup.noGenerators());
			}

			ProgressPrinter.println("Finding largest valid subgroup");
			
			gapWriter.write("C := RightTransversal(G,H);;\n");
			gapWriter.write("Size(C);\n");
			gapWriter.flush();

			int noCosets = Integer.parseInt(gapReader.readLine());
			
			ProgressPrinter.println("No cosets: " + noCosets);

			int j = 2;
			long initialTime = System.currentTimeMillis();
			while (j <= noCosets && (Config.TIME_BOUND==0 || (System.currentTimeMillis()-initialTime < Config.TIME_BOUND))) {
				gapWriter.write("C[" + j + "];\n");
				gapWriter.flush();

				Permutation nextRepresentative = getPerm();

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
			largestValidSubgroup = getFinalGroupFromGAP();

			if(Config.TESTING_IN_PROGRESS) {
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
			}
	
			if(Config.PROFILE) {
				Profile.LARGEST_VALID_END = System.currentTimeMillis();
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				ProgressPrinter.println("Size of largest valid subgroup: " + gapReader.readLine());
			}
		} else {
			largestValidSubgroup = baseGroup;

			if(Config.DETECT_ONLY && Config.TESTING_IN_PROGRESS) {
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
			}
			
			
			if(!Config.DETECT_ONLY) {
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");

				if(Config.TESTING_IN_PROGRESS) {
					gapWriter.write("Size(H);\n");
					gapWriter.flush();
					sizeOfLargestValidSubgroup  = Long.parseLong(gapReader.readLine());
				}
			
			} else if(Config.PROFILE) {
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

	private Group getFinalGroupFromGAP() throws IOException {
		gapWriter.write("Size(GeneratorsOfGroup(H));\n");
		gapWriter.write("Print(JoinStringsWithSeparator(GeneratorsOfGroup(H),\"\\n\"),\"\\n\");\n");
		gapWriter.flush();

		int noGenerators = Integer.parseInt(gapReader.readLine());

		Set<Permutation> generators = new HashSet<Permutation>();
		for(int i=0; i<noGenerators; i++) {
			generators.add(getPerm());
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

	private Permutation getPerm() throws IOException {
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

	private void enlargeBaseGroupWithRandomConjugates(int noGenerators) throws IOException {

		for (int l = 1; l <= Config.NO_CONJUGATES; l++) {
			gapWriter.write("alpha := Random(G);;\n");
			for (int j = 1; j <= noGenerators; j++) {
				gapWriter.write("(alpha^-1) * (GeneratorsOfGroup(H)[" + j
						+ "]) * alpha;\n");
			}
			
			gapWriter.flush();
			
			for(int j = 1; j <= noGenerators; j++) {
				Permutation pe = getPerm();
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
			FileWriter fw = new FileWriter(Config.COMMON+"graph.saucy");
			fw.write(extractor.directedSaucyRepresentation());
			fw.close();
		} catch(FileNotFoundException e) {
			System.out.println("Error while trying to create file \"" + Config.COMMON+"graph.saucy\".  Make sure that the directory " + Config.COMMON + " exists, and that you have write permission.");
			System.exit(1);
		} catch (IOException e) {
			System.out.println("An error occurred while trying to create the file \"" + Config.COMMON+"graph.saucy\".");
			System.exit(1);
		}
		
		ProgressPrinter.println("Computing the group Aut(C(P)) using directed saucy.");
		String saucyGenerators = computeAutomorphismsOfDirectedGraph(Config.COMMON+"graph.saucy");
		
		autSCD = new Group(saucyGenerators, extractor);
	}

	private static String computeAutomorphismsOfDirectedGraph(String filename) {

		String result = "";
		
		String saucyString; 
		if(Config.isOSWindows()) {
			saucyString = Config.SAUCY + " -d \"" + filename + "\"";
		} else {
			saucyString = Config.SAUCY + " -d " + filename;
		}

		ProgressPrinter.println("\nLaunching saucy via the following command: " + saucyString + "\n");
		
		Process saucy = CommunicatingProcess.create(saucyString);

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
		
		if(Config.PROFILE) { Profile.GAP_LAUNCH_START = System.currentTimeMillis(); }

		String gapString;

		if(Config.isOSWindows()) {
			gapString = Config.GAP + " -L \"" + Config.COMMON + "gapworkspace\" -q";
		} else {
			gapString = Config.GAP + " -L " + Config.COMMON + "gapworkspace -q";
		}
		ProgressPrinter.printSeparator();
		ProgressPrinter.print("Starting GAP with command: " + gapString + "\n");

		gap = CommunicatingProcess.create(gapString);
		
		gapReader = CommunicatingProcess.getReader(gap);
		gapWriter = CommunicatingProcess.getWriter(gap);

		ErrorStreamHandler esh = new ErrorStreamHandler(gap, "\nGAP produced errors:\n====================",  "End of GAP errors", true);
		esh.start();
		
		gapWriter.write("0;\n");
		gapWriter.flush();

		ProgressPrinter.println("Output produced by GAP at startup:");
		String line = gapReader.readLine();
		while(!line.equals("0")) {
			
			ProgressPrinter.println(line);
			if(line.contains("Couldn't open saved workspace")) {
				ProgressPrinter.println("Error -- bad GAP workspace specified in configuration file.");
			}
			
			line = gapReader.readLine();
		}
		
		if(Config.PROFILE) { Profile.GAP_LAUNCH_END = System.currentTimeMillis(); }

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
