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

import src.etch.error.ErrorTable;
import src.promela.lexer.Lexer;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.utilities.Config;
import src.utilities.Profile;

import java.io.*;

public class Check {


	/** The AST representing the source program. */
	protected Node theAST;
	protected String sourceName;
	
	public Check(String sourceName) {

		if(Config.PROFILE) { Profile.PARSE_START = System.currentTimeMillis(); }

		this.sourceName = sourceName;
		Lexer scanner = null;
	
		try {
			scanner = new Lexer(new PushbackReader(new BufferedReader(
					new FileReader(sourceName)), 1024));
		} catch (FileNotFoundException e) {
			System.out.println("Can't access source file " + sourceName);
			System.exit(1);
		}

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
		chk.unify();
		
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
