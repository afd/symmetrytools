package src.symmreducer;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.StringTokenizer;

import junit.framework.Assert;
import src.etch.unifier.Substituter;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.SymmExtractor;
import src.utilities.Config;
import src.utilities.Profile;
import src.utilities.Strategy;
import src.utilities.StringHelper;

public class SymmReducer extends SymmExtractor {

	public SymmReducer(String sourceName) throws IOException {
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
    		System.exit(0);
    	}
    	
    	if(Config.PROFILE) { Profile.CLASSIFY_START = System.currentTimeMillis(); }

    	Assert.assertNotNull(gap);
    	
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
    			System.out.println("Full symmetry group detected!  Symmetric markers only partially supported.");
    		}
    		break;
    	default:
    		Assert.assertTrue(false);
    	}
    	
    	// Ensure that GAP has finished processing before running the perl program
    	gapWriter.write("Size(H);\n");
    	gapWriter.write("GeneratorsOfGroup(H);\n");

    	gapWriter.flush();

    	System.out.println("Size of group: " + gapReader.readLine());
    	
		String groupGenerators = "";
		String temp = gapReader.readLine();

		while (!temp.contains(new String("]"))) {
			groupGenerators = groupGenerators + temp;
			temp = gapReader.readLine();
		}
		groupGenerators = groupGenerators + temp;

    	groupGenerators = removeSpaces(groupGenerators);

    	if(Config.PROFILE) { Profile.CLASSIFY_END = System.currentTimeMillis(); 	}
    	
    	String command;

    	if(Config.isOSWindows()) {
    		command = "perl \"" + Config.COMMON + "PreparePan.pl\" \"" + sourceName + "\" " + extractor.getNoProcesses() + " " + extractor.getStaticChannelNames().size() + " groupinfo " + (Config.USE_TRANSPOSITIONS?"true":"false") + " " + (Config.USE_STABILISER_CHAIN?"true":"false") + " " + Config.REDUCTION_STRATEGY + " \"" + StringHelper.doubleUpSlashes(Config.COMMON) + "\" \" " + groupGenerators + "\"";
    	} else {
    		command = "perl " + Config.COMMON + "PreparePan.pl " + sourceName + " " + extractor.getNoProcesses() + " " + extractor.getStaticChannelNames().size() + " groupinfo " + (Config.USE_TRANSPOSITIONS?"true":"false") + " " + (Config.USE_STABILISER_CHAIN?"true":"false") + " " + Config.REDUCTION_STRATEGY + " " + Config.COMMON + " \"" + groupGenerators + "\"";
    	}

    	if(Config.PROFILE) { Profile.CODE_GENERATION_START = System.currentTimeMillis(); 	}

    	System.out.println(command);
    	
	 	Process perl = Runtime.getRuntime().exec(command);
	 	
	 	try {	
			perl.waitFor();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		if(Config.REDUCTION_STRATEGY==Strategy.EXACTMARKERS || (Config.REDUCTION_STRATEGY!=Strategy.APPROXMARKERS && Config.USE_TRANSPOSITIONS)) {
			new SymmetryApplierTranspositions(extractor).applySymmetry("sympan.c");
		} else {
			new SymmetryApplierBasic(extractor).applySymmetry("sympan.c");
		}
		
    	if(Config.PROFILE) { Profile.CODE_GENERATION_END = System.currentTimeMillis(); 	}

    }

	private StaticChannelDiagramExtractor parseUserSpecifiedSymmetry() throws FileNotFoundException, IOException {
		startGAP();
		StaticChannelDiagramExtractor extractor;
		Assert.assertNotNull(Config.AUTOS_FILE);
		extractor = new StaticChannelDiagramExtractor();
		if(isWellTyped(true)) {
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
