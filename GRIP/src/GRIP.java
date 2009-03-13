package src;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PushbackReader;

import src.symmetricprism.lexer.Lexer;
import src.symmetricprism.lexer.LexerException;
import src.symmetricprism.node.Node;
import src.symmetricprism.parser.Parser;
import src.symmetricprism.parser.ParserException;
import src.translator.Abstractor;
import src.translator.Translator;

public class GRIP {

	public static void main(String[] args) {

		boolean optimise = false;
		boolean eliminate = false;

		if (args.length < 2) {
			showArgumentsError();
		}
		
		String inputFile = null;
		String outputFile = null;

		String logicInputFile = null;
		String logicOutputFile = null;
			
		int argsCounter = 0;
		while(args[argsCounter].equals("-optimise")||args[argsCounter].equals("-eliminate")) {
			if(args[argsCounter].equals("-optimise")) {
				optimise = true;
			} else {
				eliminate = true;
			}
			argsCounter++;
		}
			
		if(!(((args.length-argsCounter)==2)||((args.length-argsCounter)==4))) {
			showArgumentsError();
		}

		inputFile = args[argsCounter];
		outputFile = args[argsCounter+1];
			
		if(args.length-argsCounter==4) {
			logicInputFile = args[argsCounter+2];
			logicOutputFile = args[argsCounter+3];
		}
		
		try {
			translateSpecification(optimise, eliminate, inputFile, outputFile, logicInputFile, logicOutputFile);
		} catch (FileNotFoundException e) {
			System.out.println("Can't access source file " + inputFile + ((null != logicInputFile) ? " or properties file " + logicInputFile : ""));
			System.exit(1);
		} catch (ParserException e) {
			System.out.println("Parser error:");
			e.printStackTrace();
		} catch (LexerException e) {
			System.out.println("Lexer error:");
			e.printStackTrace();
		} catch (IOException e) {
			System.out.println("I/O error:");
			e.printStackTrace();
		}

	
	}

	private static void showArgumentsError() {
		System.out.println("\nUsage:\n\nGRIP [ -optimise, -eliminate ] <original> <reduced> [ <original-properties> <reduced-properties> ]");
		System.exit(0);
	}

	public static void translateSpecification(boolean optimise, boolean eliminate, String inputFile, String outputFile, String logicInputFile, String logicOutputFile) throws ParserException, LexerException, IOException {
		System.out.println("\nTranslating model: \"" + inputFile + "\"");
		
		Lexer scanner = null;
		scanner = new Lexer(new PushbackReader(new BufferedReader(
				new FileReader(inputFile)), 1024));

		Parser parser = new Parser(scanner);

		Translator translator = new Translator(outputFile, optimise, eliminate);

		Node modelAST = parser.parse();
		if (optimise) {
			modelAST.apply(new Abstractor());
		}
		modelAST.apply(translator);
			
		System.out.println(" -> Reduced model: \"" + outputFile + "\"");
			
			
		if(logicInputFile!=null) {
			System.out.println("\nTranslating properties: \"" + logicInputFile + "\"");
			System.out.println("Can't access source file " + logicInputFile);
			System.exit(1);
			
			parser = new Parser(scanner);
			Node propertiesAST = parser.parse();
			if (optimise) {
				propertiesAST.apply(new Abstractor());
			}
			translator.setLogicOutputFile(logicOutputFile);
			propertiesAST.apply(translator);
				
			System.out.println(" -> Reduced properties: \"" + logicOutputFile + "\"");
		
		}
	}

}
