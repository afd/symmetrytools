package src.symmextractor;

import java.io.BufferedReader;
import java.io.BufferedWriter;
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
import src.promela.parser.Parser;
import src.utilities.CommunicatingProcess;
import src.utilities.Config;
import src.utilities.Profile;


public class SymmExtractor extends Check {

	protected Process gap;
	protected BufferedReader gapReader;
	protected BufferedWriter gapWriter;
	private StaticChannelDiagramExtractor extractor;
	private Group autSCD;
	private Group largestValidSubgroup;
	
	public SymmExtractor(String sourceName) throws IOException {
		super(sourceName);
	}

	public StaticChannelDiagramExtractor extract() throws IOException {

		if(Config.PROFILE) { Profile.EXTRACT_START = System.currentTimeMillis(); }
		extractor = new StaticChannelDiagramExtractor();
		if(isWellTyped(true)) {
			System.out.println("Reparsing source without inlines");
			reparseSourceWithoutInlines();
			theAST.apply(extractor);
			Substituter substituter = extractor.unify();
			applyTypeSubstitutions(extractor, substituter);
			if(Config.PROFILE) { Profile.EXTRACT_END = System.currentTimeMillis(); }

			if(Config.PROFILE) { Profile.SAUCY_START = System.currentTimeMillis(); }
			computeStaticChannelDiagramAutomorphisms(extractor);
			if(Config.PROFILE) { Profile.SAUCY_END = System.currentTimeMillis(); }
			
			System.out.println("  Aut(C(P)) = " + autSCD);

			if(Config.PROFILE) { Profile.LARGEST_VALID_START = System.currentTimeMillis(); }
			computeLargestValidSubgroup();

			System.out.println("H = " + largestValidSubgroup);
			System.out.println("      is a safe group for symmetry reduction.");

			return extractor;
		}
		if(Config.PROFILE) { Profile.EXTRACT_END = System.currentTimeMillis(); }
		return null;
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
		System.out.println("Computing safe generators");
		Set<Permutation> safeGenerators = new HashSet<Permutation>();
				
		for(Iterator<Permutation> i = autSCD.iterator(); i.hasNext();) {
			Permutation alpha = i.next();
			if (alpha.isSafeFor(theAST, extractor)) {
				System.out.println("    " + alpha + " : valid");
				safeGenerators.add(alpha);
			} else {
				System.out.println("    " + alpha + " : not valid");
				someGeneratorsInvalid = true;
			}
		}
		Group baseGroup = new Group(safeGenerators);

		if(someGeneratorsInvalid) {
			startGAP();

			// Send Aut(SCD) = G to GAP, and H, the initial valid subgroup.
			gapWriter.write("G := " + autSCD.gapGenerators(extractor) + ";\n");
			gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");


			if(Config.PROFILE) {
				gapWriter.write("Size(G);\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				System.out.println("Size of Aut(SCD(P)): " + gapReader.readLine());
				System.out.println("Size of base group: " + gapReader.readLine());
			}
			
			
			if(Config.NO_CONJUGATES>0) {
				enlargeBaseGroupWithRandomConjugates(baseGroup.noGenerators());
			}

			System.out.println("Finding largest valid subgroup");
			
			gapWriter.write("C := RightTransversal(G,H);;\n");
			gapWriter.write("Size(C);\n");
			gapWriter.flush();

			int noCosets = Integer.parseInt(gapReader.readLine());
			
			System.out.println("No cosets: " + noCosets);

			int j = 2;
			long initialTime = System.currentTimeMillis();
			while (j <= noCosets && (Config.TIME_BOUND==0 || (System.currentTimeMillis()-initialTime < Config.TIME_BOUND))) {
				gapWriter.write("C[" + j + "];\n");
				gapWriter.flush();

				Permutation nextRepresentative = getPerm();

				if (nextRepresentative.isSafeFor(theAST, extractor)) {
					System.out.println("    " + nextRepresentative + " : valid");
					addRepresentativeToGenerators(j);
					int newNoCosets = recomputeCosetRepresentatives(noCosets,j);
					if(newNoCosets!=-1) {
						noCosets = newNoCosets;
						System.out.println("No cosets: " + noCosets);
						j = 2;
					} else {
						System.out.println("No cosets: " + (noCosets-j));
						j++;
					}
				} else {
					j++;
				}
			}
			largestValidSubgroup = getFinalGroupFromGAP();
			if(Config.PROFILE) {
				Profile.LARGEST_VALID_END = System.currentTimeMillis();
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				System.out.println("Size of largest valid subgroup: " + gapReader.readLine());
			}
		} else {
			largestValidSubgroup = baseGroup;
			if(!Config.DETECT_ONLY) {
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");
			} else if(Config.PROFILE) {
				Profile.LARGEST_VALID_END = System.currentTimeMillis();
				startGAP();
				gapWriter.write("H := " + baseGroup.gapGenerators(extractor) + ";\n");
				gapWriter.write("Size(H);\n");
				gapWriter.flush();
				System.out.println("Size of Aut(SCD(P)): " + gapReader.readLine());
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
			StaticChannelDiagramExtractor extractor) throws IOException {
		FileWriter fw = new FileWriter(Config.TEMP_FILES+"graph.saucy");
		fw.write(extractor.directedSaucyRepresentation());
		fw.close();
		System.out.println("Computing the group Aut(C(P)) using directed saucy.");
		String saucyGenerators = computeAutomorphismsOfDirectedGraph(Config.TEMP_FILES+"graph.saucy");
		autSCD = new Group(saucyGenerators, extractor);
	}

	private static String computeAutomorphismsOfDirectedGraph(String filename) {

		String result = "";
		
		try {
			Process saucy;
			if(Config.isOSWindows()) {
				saucy = CommunicatingProcess.create(Config.SAUCY + " -d \"" + filename + "\"");
			} else {
				saucy = CommunicatingProcess.create(Config.SAUCY + " -d " + filename);
			}

			BufferedReader br = CommunicatingProcess.getReader(saucy);
			String temp;
			try {
				while ((temp = br.readLine()) != null) {
					result += temp + "\n";
				}
				br.close();
			} catch (IOException ioe) {
				System.out.println("Error while getting output from saucy.");
			}

		} catch (IOException e) {
			System.out.println("Error reading input for saucy");
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
		System.out.println("Starting GAP");

		if(Config.isOSWindows()) {
			gap = CommunicatingProcess.create(Config.GAP + " -L \"" + Config.COMMON + "gapworkspace\" -q");
		} else {
			gap = CommunicatingProcess.create(Config.GAP + " -L " + Config.COMMON + "gapworkspace -q");
		}
		
		gapReader = CommunicatingProcess.getReader(gap);
		gapWriter = CommunicatingProcess.getWriter(gap);

		gapWriter.write("0;\n");
		gapWriter.flush();
		
		while(!gapReader.readLine().equals("0"));
		if(Config.PROFILE) { Profile.GAP_LAUNCH_END = System.currentTimeMillis(); }

	}

	public void printGAPError() throws IOException {
		System.out.println((new BufferedReader(new InputStreamReader(gap.getErrorStream()))).readLine());
	}

}
