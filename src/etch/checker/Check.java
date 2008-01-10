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
			br = getBufferForInputSpecification(sourceName);
		} catch (FileNotFoundException e1) {
			System.out.println("Can't access source file " + sourceName);
			System.exit(1);
		}
		
		try {
			theAST = new Parser(new Lexer(new PushbackReader(br, 1024))).parse();
		} catch (Exception e) {
			System.out.println(e);
			System.exit(1);
		}
		
		if(Config.PROFILE) { Profile.PARSE_END = System.currentTimeMillis(); }

	}

	public static BufferedReader getBufferForInputSpecification(String sourceName) throws FileNotFoundException {
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
			br = new BufferedReader(new FileReader(sourceName));
		}
		return br;
	}

	public boolean isWellTyped(boolean isPidSensitive) {
		Checker chk = new Checker(isPidSensitive);
		theAST.apply(chk);
		Substituter substituter = chk.unify();
	
		if (chk.getErrorTable().hasErrors()) {
			System.out.println(chk.getErrorTable().output("while processing " + sourceName));
			return false;
		}

		System.out.println("Program is well typed");

		substituter.setTypeInformation(chk);
		theAST.apply(substituter);
		chk.printCompleteTypeInformation(sourceName);

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
