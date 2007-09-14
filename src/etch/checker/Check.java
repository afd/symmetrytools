/****************************************************************************/
/*                 ETCH: An Enhanced Type Checker for Promela               */
/*                                                                          */
/*                   Copyright 2003 University of Glasgow                   */
/*                                                                          */
/*                           All rights reserved.                           */
/*                                                                          */
/****************************************************************************/

/****************************************************************************/
/* FILE          : Main.java                                                */
/* DESCRIPTION   : Top-level driver for ETCH                                */
/****************************************************************************/

package src.etch.checker;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PushbackReader;
import java.io.StringReader;

import src.etch.error.ErrorTable;
import src.etch.typeinference.Substituter;
import src.promela.lexer.Lexer;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.utilities.Config;
import src.utilities.Profile;

public class Check {


	/** The AST representing the source program. */
	protected Node theAST;
	protected String sourceName;
	
	public Check(String sourceName) {

		if(Config.PROFILE) { Profile.PARSE_START = System.currentTimeMillis(); }

		this.sourceName = sourceName;

		BufferedReader br = null;
		try {
			Process p = Runtime.getRuntime().exec("cpp " + sourceName);
			BufferedReader cppReader = new BufferedReader(new InputStreamReader(p.getInputStream()));
			String programForParsing = "";
			String line;
			int currentLine = 1;
			while((line=cppReader.readLine())!=null) {
				if(line.length() > 0 && line.charAt(0)=='#') {
					String[] splitOnSpace = line.split(" ");
					int nextLine = Integer.parseInt(splitOnSpace[1]);
					for(;currentLine<nextLine; currentLine++) {
						programForParsing += "\n";
					}
				} else {
					programForParsing += line + "\n";
					currentLine++;
				}
				
			}
			br = new BufferedReader(new StringReader(programForParsing));
		} catch (IOException e) {
			System.out.println("C preprocessor not available");
			try {
				br = new BufferedReader(new FileReader(sourceName));
			} catch (FileNotFoundException e1) {
				System.out.println("Can't access source file " + sourceName);
				System.exit(1);
			}
		}
		
		Lexer scanner = new Lexer(new PushbackReader(br, 1024));

		Parser parser = new Parser(scanner);

		try {
			theAST = parser.parse();
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
		
		if(Config.PROFILE) { Profile.PARSE_END = System.currentTimeMillis(); }

	}

	public boolean isWellTyped(boolean isPidSensitive) {
		Checker chk = new Checker(isPidSensitive);
		theAST.apply(chk);
		Substituter substituter = chk.unify();
		substituter.setTypeInformation(chk);
		theAST.apply(substituter);

		chk.printCompleteTypeInformation();
		
		//		VariableAnalyser analyser = new VariableAnalyser(chk);
//		theAST.apply(analyser);
		
		ErrorTable errorTable = chk.getErrorTable();
		if (errorTable.hasErrors()) {
			System.out.println(errorTable.output("while processing " + sourceName));
			return false;
		}

		System.out.println("Program is well typed");
		return true;
	}

	public static void main(String[] args) {

		if (args.length < 1) {
			System.out.println("Usage: check filename");
			System.exit(1);
		}

		boolean isPidSensitive = (args.length > 1) && (args[1].equals("-symm"));

		new Check(args[0]).isWellTyped(isPidSensitive);
	}
}
