package src;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PushbackReader;

import src.symmetricprism.lexer.Lexer;
import src.symmetricprism.node.Node;
import src.symmetricprism.parser.Parser;
import src.translator.Abstractor;
import src.translator.ModelType;
import src.translator.Translator;

public class GRIP {

	public static void main(String[] args) {

		boolean optimise = false;
		boolean eliminate = false;

		if (args.length < 2) {
			showArgumentsError();
		}

/*		if (args[0].equals("-template")) {
			generateTemplate(args);
		} else {*/
		
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

		System.out.println("\nTranslating model: \"" + inputFile + "\"");
			
		Lexer scanner = null;
		try {
			scanner = new Lexer(new PushbackReader(new BufferedReader(
					new FileReader(inputFile)), 1024));
		} catch (FileNotFoundException e) {
			System.out.println("Can't access source file " + inputFile);
			System.exit(1);
		}

		Parser parser = new Parser(scanner);

		Translator translator = new Translator(outputFile, optimise, eliminate);
		try {
			Node theAST = parser.parse();
			if (optimise) {
				theAST.apply(new Abstractor());
			}
			theAST.apply(translator);
		} catch (Exception e) {
			System.out.println(e);
		e.printStackTrace();
		System.exit(1);
		}
			
		System.out.println(" -> Reduced model: \"" + outputFile + "\"");
			
			
		if(logicInputFile!=null) {
				System.out.println("\nTranslating properties: \"" + logicInputFile + "\"");
			try {
				scanner = new Lexer(new PushbackReader(new BufferedReader(
					new FileReader(logicInputFile)), 1024));
			} catch (FileNotFoundException e) {
				System.out.println("Can't access source file " + logicInputFile);
				System.exit(1);
			}
			
			parser = new Parser(scanner);
			try {
				Node theAST = parser.parse();
				if (optimise) {
					theAST.apply(new Abstractor());
				}
				translator.setLogicOutputFile(logicOutputFile);
				theAST.apply(translator);
			} catch (Exception e) {
				System.out.println(e);
				e.printStackTrace();
				System.exit(1);
			}
				
			System.out.println(" -> Reduced properties: \"" + logicOutputFile + "\"");
		
		}
	
	}


	@SuppressWarnings("unused")
	private static void generateTemplate(String[] args) {
		if (args.length != 5) {
			showArgumentsError();
		}

		ModelType type = null;
		if (args[4].equals("mdp")) {
			type = ModelType.nondeterministic;
		} else if (args[4].equals("dtmc")) {
			type = ModelType.probabilistic;
		} else {
			showArgumentsError();
		}

		try {
			String filename = args[1];
			int n = Integer.parseInt(args[2]);
			int k = Integer.parseInt(args[3]);
			if (k < 0 || n < 1) {
				showArgumentsError();
			}

			try {
				FileWriter fw = new FileWriter(filename);

				fw.write(String.valueOf(type));

 				fw.write("\n\nmodule process1\n\n");
				fw.write("  s1 : [0.." + k + "] init 0;\n\n");
				fw.write("  // Statements\n\n");
				fw.write("endmodule\n\n");

				for (int i = 2; i <= n; i++) {
					fw.write("module process" + i + " = process1 [ s1=s" + i
							+ ", s" + i + "=s1] endmodule\n");
				}

				fw.close();

			} catch (IOException e) {
				System.out.println("Error writing to " + filename);
				e.printStackTrace();
				System.exit(1);
			}
		} catch (NumberFormatException e) {
			showArgumentsError();
		}
	}

	private static void showArgumentsError() {
		System.out.println("\nUsage:\n\nGRIP [ -optimise, -eliminate ] <original> <reduced> [ <original-properties> <reduced-properties> ]");
		System.exit(0);
	}

}
