package src.symmreducer;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.StringTokenizer;


import src.etch.typeinference.Substituter;
import src.promela.lexer.LexerException;
import src.promela.parser.ParserException;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.SymmExtractor;
import src.utilities.Config;
import src.utilities.Profile;
import src.utilities.ProgressPrinter;

public class SymmReducer extends SymmExtractor {

	public SymmReducer(String sourceName) throws IOException, ParserException, LexerException {
		super(sourceName);
	}

    public void reduce() throws IOException {
    	
    	StaticChannelDiagramExtractor extractor;

    	if(!Config.AUTOMATIC_DETECTION) {
        	// TODO Typecheck first
    		extractor = parseUserSpecifiedSymmetry();
    	}
    	else {
    		extractor = extract();
    	}

    	if(extractor==null) {
    		System.exit(1);
    	}

    	ProgressPrinter.println("Generating symmetry reduction algorithms\n");
    	
    	if(Config.PROFILE) { Profile.CLASSIFY_START = System.currentTimeMillis(); }

    	assert(null != gap);
    	
    	if(!Config.USE_TRANSPOSITIONS) {
    		gapWriter.write("useTranspositions := false;;\n");
    	}
    	
    	if(!Config.USE_STABILISER_CHAIN) {
    		gapWriter.write("useStabiliserChain := false;;\n");
    	}

    	switch (Config.REDUCTION_STRATEGY) {
    	case FAST:
    	case SEGMENT:
    	case FLATTEN:
    		gapWriter.write("ClassifyBest(H,\"groupinfo\");\n");
    		break;
    	case ENUMERATE:
    		gapWriter.write("ClassifyEnumerate(H,\"groupinfo\");\n");
    		break;
    	case HILLCLIMBING:
    		gapWriter.write("ClassifyLocalSearch(H,\"groupinfo\");\n");
    		break;
    	case EXACTMARKERS:
    	case APPROXMARKERS:
    		gapWriter.write("H = SymmetricGroup(" + (extractor.getNoProcesses()-1) + ");\n");
    		gapWriter.flush();
    		
    		if(!Boolean.parseBoolean(gapReader.readLine())) {
    			System.out.println("Symmetric markers only work with a full symmetry group, i.e. the group Sym({1,..," + (extractor.getNoProcesses()-1) + ")");
    			System.exit(0);
    		} else {
    			ProgressPrinter.println("Full symmetry group detected - symmetry markers can be applied");
    			if(!Config.USE_TRANSPOSITIONS) {
    				System.out.println("Transpositions must be used with this strategy - switch made automatically");
    				Config.USE_TRANSPOSITIONS = true;
    			}
    		
    		}
    		break;
    	default:
    		assert(false);
    	}

    	// Ensure that GAP has finished processing before running the perl program
    	gapWriter.write("Size(H);\n");
    	gapWriter.write("GeneratorsOfGroup(H);\n");

    	gapWriter.flush();

    	ProgressPrinter.println("The symmetry group has size " + gapReader.readLine());
    	
		String groupGenerators = "";
		String temp = gapReader.readLine();

		while (!temp.contains(new String("]"))) {
			groupGenerators = groupGenerators + temp;
			temp = gapReader.readLine();
		}
		groupGenerators = groupGenerators + temp;

    	groupGenerators = removeSpaces(groupGenerators);

    	if(Config.PROFILE) { Profile.CLASSIFY_END = System.currentTimeMillis(); 	}
    	
    	if(Config.PROFILE) { Profile.CODE_GENERATION_START = System.currentTimeMillis(); 	}

    	SymmetryApplier symmetryApplier;
    	
    	if(Config.PARALLELISE) {
    		symmetryApplier = new SymmetryApplierParallel(sourceName, extractor, groupGenerators);
    	} else {
    		symmetryApplier = new SymmetryApplier(sourceName, extractor, groupGenerators);
    	}
    	
    	symmetryApplier.applySymmetry();
    	
    	if(Config.PROFILE) { Profile.CODE_GENERATION_END = System.currentTimeMillis(); 	}

    	ProgressPrinter.printSeparator();
    	ProgressPrinter.println("Completed generation of sympan verifier which includes algorithms for symmetry reduction!\n");
    	ProgressPrinter.println("To generate an executable verifier use the following command:");
    	ProgressPrinter.print("   gcc -o sympan sympan.c group.c");
    	    	
    	if(Config.PARALLELISE) {
    		ProgressPrinter.print(" symmetry_threads.c -DNUM_THREADS=...");
    	}
    	
    	ProgressPrinter.println("");
    	ProgressPrinter.println("together with SPIN compile-time directives for your specification.\n");
    	ProgressPrinter.println("Execute the verifier using the following command:");
		if(Config.isOSWindows()) {
			ProgressPrinter.println("   sympan.exe");
		} else {
			ProgressPrinter.println("   ./sympan");
		}
		ProgressPrinter.println("together with SPIN run-time options for your specification.");
		
    }

	private StaticChannelDiagramExtractor parseUserSpecifiedSymmetry() throws FileNotFoundException, IOException {
		startGAP();
		StaticChannelDiagramExtractor extractor;
		assert(null != Config.AUTOS_FILE);
		extractor = new StaticChannelDiagramExtractor();
		if(typecheck(true)) {
			System.out.println("Reparsing source without inlines");
			reparseSourceWithoutInlines();
			theAST.apply(extractor);
			Substituter substituter = extractor.unify();
			applyTypeSubstitutions(extractor, substituter);
			
			BufferedReader gensReader = new BufferedReader(new FileReader(Config.AUTOS_FILE));
			
			gapWriter.write("H := Group(");

			for(String line = gensReader.readLine(); ; ) {
				String generator = "";
				StringTokenizer permSplitter = new StringTokenizer(line,"()");
				while(permSplitter.hasMoreTokens()) {
					generator += "(";
					StringTokenizer cycleSplitter = new StringTokenizer(permSplitter.nextToken()," ");
					while(cycleSplitter.hasMoreTokens()) {
						generator += extractor.getGapNumber(cycleSplitter.nextToken());
						if(cycleSplitter.hasMoreTokens()) {
							generator += ",";
						}
					}
					generator += ")";
				}
				gapWriter.write(generator);
				line = gensReader.readLine();
				if(line!=null) {
					gapWriter.write(",");
				} else {
					break;
				}
			}

			gapWriter.write(");;\n");

		}
		return extractor;
	}
    
    private String removeSpaces(String s) {
    	String result = "";
    	for(int i=0; i<s.length(); i++) {
    		if(s.charAt(i)!=' ') {
    			result += s.charAt(i);
    		}
    	}
		return result;
	}

}
