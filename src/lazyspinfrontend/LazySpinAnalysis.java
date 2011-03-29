package src.lazyspinfrontend;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PushbackReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import src.etch.checker.Check;
import src.etch.checker.Checker;
import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.VarEntry;
import src.etch.typeinference.ConstraintSet;
import src.etch.typeinference.Substituter;
import src.etch.typeinference.Unifier;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.EtchTypeFactory;
import src.etch.types.VisibleType;
import src.promela.lexer.Lexer;
import src.promela.lexer.LexerException;
import src.promela.node.Node;
import src.promela.parser.Parser;
import src.promela.parser.ParserException;
import src.symmextractor.PidAwareChecker;
import src.symmextractor.types.PidType;
import src.symmreducer.InsensitiveVariableReference;
import src.symmreducer.PidIndexedArrayReference;
import src.symmreducer.PidSwapper;
import src.symmreducer.SensitiveVariableReference;
import src.symmreducer.SymmetryApplier;
import src.utilities.BooleanOption;
import src.utilities.Config;
import src.utilities.ProgressPrinter;
import src.utilities.Strategy;

public class LazySpinAnalysis {

	public static boolean FULL_REDUCTION = false;
	public static boolean USE_MARKERS = false;
	
	/**
	 * @param args
	 * @throws IOException 
	 */
	public static void main(String[] args) throws IOException {
		
		PidAwareChecker.HACK_FOR_SPIN_2011 = true;
		
		if(args.length < 1 || args.length > 3)
		{
			System.out.println("Error - usage: LazySpinAnalysis [full,markers] <file>");
			System.exit(1);
		}
		
		int argNo;
		for(argNo = 0; argNo < args.length - 1; argNo++)
		{
			if(args[argNo].equals("full")) {
				FULL_REDUCTION = true;
			} else if(args[argNo].equals("markers")) {
				USE_MARKERS = true;
				System.out.println("Symmetry marker support not yet implemented.");
				System.exit(1);
			} else {
				System.out.println("Ignoring unknown option: " + args[argNo]);
			}
				
		}
		
		final String sourceName = args[argNo];

		Config.resetConfiguration();
		Config.setUnspecifiedOptionsToDefaultValues();
		Config.initialiseCommandLineSwitches();
		Config.setBooleanOption(BooleanOption.VERBOSE, true);
		
		BufferedReader br = null;
		try {
			br = Check.getBufferForInputSpecification(sourceName);
		} catch (FileNotFoundException e) {
			ProgressPrinter.println("Cannot access source file " + sourceName);
			System.exit(1);
		}
		
		Node theAST = null;
		
		try {
			theAST = new Parser(new Lexer(new PushbackReader(br, 1024))).parse();
		} catch (ParserException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (LexerException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
		
		Checker checker = new Checker(new EtchTypeFactory(), new ConstraintSet(new Unifier()));
		theAST.apply(checker);
		if(checker.getErrorTable().hasErrors())	{
			System.err.println(checker.getErrorTable().output("while processing " + sourceName, sourceName));
			System.exit(1);
		}
		
		LazySpinFindNumProcesses findNumProcesses = new LazySpinFindNumProcesses();
		theAST.apply(findNumProcesses);

		LazySpinChecker repGenerator = new LazySpinChecker(findNumProcesses);
		theAST.apply(repGenerator);

		Substituter substituter = repGenerator.unify();
		
		substituter.setTypeInformation(repGenerator);
		
		if(repGenerator.getErrorTable().hasErrors()) {
			System.err.println(repGenerator.getErrorTable().output("while processing " + sourceName, sourceName));
			System.exit(1);
		}
		
		theAST.apply(substituter);
		
		OutputStreamWriter os = new OutputStreamWriter(System.out);		
		
		final String N = "LAZYSPIN_NUM_PROCESSES";
		
		os.write("#define " + N + " " + LazySpinChecker.numberOfRunningProcesses() + "\n\n");
		os.write("State min_now; // Global state used as target for state canonization\n\n");

		SymmetryApplier.writePreprocessorMacros(os);
		
		PidSwapper pidSwapper = new PidSwapper(repGenerator, os, 0, null);
		pidSwapper.writeApplyPrSwapToState("State");
		
		writeSameCell(os);

		writeLessThan(repGenerator, os);

		if(FULL_REDUCTION)
		{
			writeEquallyInsensitive(repGenerator, os);
		}
		
		writeRep(os, N);

		writeSymHash(repGenerator, os);

		os.flush();
		
	}

	private static void writeEquallyInsensitive(LazySpinChecker repGenerator,
			OutputStreamWriter os) throws IOException {
		os.write("int equally_insensitive(State* s, int i, int j)\n");
		os.write("{\n");
		
		os.write("  /* Id-insensitive local variables first */\n");
		
		ProctypeEntry theProctypeEntry = null;
		for(EnvEntry entry : repGenerator.getEnv().getTopEntries().values())
		{
			if(entry instanceof ProctypeEntry)
			{
				theProctypeEntry = (ProctypeEntry) entry;
				break;
			}
		}
		assert(null != theProctypeEntry);
		
		List<InsensitiveVariableReference> insensitiveVarReferencesForI = repGenerator.insensitiveVariableReferencesForProcess(theProctypeEntry, "i", "s");
		List<InsensitiveVariableReference> insensitiveVarReferencesForJ = repGenerator.insensitiveVariableReferencesForProcess(theProctypeEntry, "j", "s");

		assert(insensitiveVarReferencesForI.size() == insensitiveVarReferencesForJ.size());
		for(int ref = 0; ref < insensitiveVarReferencesForI.size(); ref++) {
			os.write("  if((" + insensitiveVarReferencesForI.get(ref) + ") != (" + insensitiveVarReferencesForJ.get(ref) + ")) return 0;\n");
		}
		
		os.write("  /* Id-insensitive global array indices second */\n");
		Map<String, EnvEntry> globalVariables = repGenerator.getGlobalVariables();

		List<InsensitiveVariableReference> insensitiveGlobalPidIndexedArrayElementsForI = new ArrayList<InsensitiveVariableReference>();
		List<InsensitiveVariableReference> insensitiveGlobalPidIndexedArrayElementsForJ = new ArrayList<InsensitiveVariableReference>();

		for(String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if(entry instanceof VarEntry && !((VarEntry)entry).isHidden() && ((VarEntry)entry).getType() instanceof ArrayType &&
					PidType.isPid((VisibleType)((ArrayType)(((VarEntry)entry).getType())).getIndexType())) {
				String prefixI = "s->" + name + "[i]";
				String prefixJ = "s->" + name + "[j]";
				insensitiveGlobalPidIndexedArrayElementsForI.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences("", ((ArrayType)((VarEntry)entry).getType()).getElementType(), prefixI, repGenerator));
				insensitiveGlobalPidIndexedArrayElementsForJ.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences("", ((ArrayType)((VarEntry)entry).getType()).getElementType(), prefixJ, repGenerator));
			}
		}

		assert(insensitiveGlobalPidIndexedArrayElementsForI.size() == insensitiveGlobalPidIndexedArrayElementsForJ.size());

		for(int ref = 0; ref < insensitiveGlobalPidIndexedArrayElementsForI.size(); ref++)
		{
			os.write("  if((" + insensitiveGlobalPidIndexedArrayElementsForI.get(ref) + ") != (" + insensitiveGlobalPidIndexedArrayElementsForJ.get(ref) + ")) return 0;\n");
		}

		os.write("  return 1;\n");
					
		os.write("}\n\n");		
	}

	private static void writeLessThan(LazySpinChecker repGenerator, OutputStreamWriter os) throws IOException {
		os.write("int less_than(State* s, State* t)\n");
		os.write("{\n");
		
		if(FULL_REDUCTION)
		{
			for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++) {
				os.write("  /* Check process " + i + "*/\n");
				os.write("  /* Id-insensitive local variables first */\n");
				List<InsensitiveVariableReference> insensitiveVarReferencesInS = repGenerator.insensitiveVariableReferencesForProcess(i, "s");
				List<InsensitiveVariableReference> insensitiveVarReferencesInT = repGenerator.insensitiveVariableReferencesForProcess(i, "t");
				assert(insensitiveVarReferencesInS.size() == insensitiveVarReferencesInT.size());
				for(int ref = 0; ref < insensitiveVarReferencesInS.size(); ref++)
				{
					os.write("  if((" + insensitiveVarReferencesInS.get(ref) + ") < (" + insensitiveVarReferencesInT.get(ref) + ")) return 1;\n");
					os.write("  if((" + insensitiveVarReferencesInS.get(ref) + ") > (" + insensitiveVarReferencesInT.get(ref) + ")) return 0;\n");
				}
				os.write("  /* Id-insensitive global array indices second */\n");
				Map<String, EnvEntry> globalVariables = repGenerator.getGlobalVariables();

				List<InsensitiveVariableReference> insensitiveGlobalPidIndexedArrayElementsInS = new ArrayList<InsensitiveVariableReference>();
				List<InsensitiveVariableReference> insensitiveGlobalPidIndexedArrayElementsInT = new ArrayList<InsensitiveVariableReference>();

				for(String name : globalVariables.keySet()) {
					EnvEntry entry = globalVariables.get(name);
					if(entry instanceof VarEntry && !((VarEntry)entry).isHidden() && ((VarEntry)entry).getType() instanceof ArrayType &&
							PidType.isPid((VisibleType)((ArrayType)(((VarEntry)entry).getType())).getIndexType())) {
						String prefixS = "s->" + name + "[" + i + "]";
						String prefixT = "t->" + name + "[" + i + "]";
						insensitiveGlobalPidIndexedArrayElementsInS.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences("", ((ArrayType)((VarEntry)entry).getType()).getElementType(), prefixS, repGenerator));
						insensitiveGlobalPidIndexedArrayElementsInT.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences("", ((ArrayType)((VarEntry)entry).getType()).getElementType(), prefixT, repGenerator));
					}
				}

				assert(insensitiveGlobalPidIndexedArrayElementsInS.size() == insensitiveGlobalPidIndexedArrayElementsInT.size());

				for(int ref = 0; ref < insensitiveGlobalPidIndexedArrayElementsInS.size(); ref++)
				{
					os.write("  if((" + insensitiveGlobalPidIndexedArrayElementsInS.get(ref) + ") < (" + insensitiveGlobalPidIndexedArrayElementsInT.get(ref) + ")) return 1;\n");
					os.write("  if((" + insensitiveGlobalPidIndexedArrayElementsInS.get(ref) + ") > (" + insensitiveGlobalPidIndexedArrayElementsInT.get(ref) + ")) return 0;\n");
				}
				
				
			}

			os.write("  return 0;\n");
			
		} else {
			os.write("  return memcmp(s, t, vsize) < 0;\n");
		}
		
		os.write("}\n\n");
	}

	private static void writeRep(OutputStreamWriter os, final String N)
			throws IOException {
		os.write("State* rep(State* orig, Perm** p)\n");
		os.write("{\n");
		os.write("  int i, j, changed;\n");
		os.write("  State temp;\n");
		os.write("  *p = perm_id(orig->_nr_pr);\n");
		os.write("  memcpy(&min_now, orig, vsize); // Representative first set to be original state\n");
		os.write("  changed = 1;\n");
		os.write("  while(changed)\n");
		os.write("  {\n");
		os.write("    changed = 0;\n");
        os.write("    for(i = 0; i < " + N + "-1; i++)\n");		
		os.write("    {\n");
        os.write("      for(j = i+1; j < " + N + "; j++)\n");		
		os.write("      {\n");
        os.write("        if(same_cell(orig, i, j))\n");		
		os.write("        {\n");
		os.write("          memcpy(&temp, &min_now, vsize);\n");
		os.write("          applyPrSwapToState(&temp, i, j);\n");
		os.write("          if(less_than(&temp, &min_now))\n");
		os.write("          {\n");
		os.write("            unsigned char t;\n");
		os.write("            changed = 1;\n");
		os.write("            memcpy(&min_now, &temp, vsize);\n");
		os.write("            t = (*p)->p_vector[i];\n");
		os.write("            (*p)->p_vector[i] = (*p)->p_vector[j];\n");
		os.write("            (*p)->p_vector[j] = t;\n");
		os.write("          }\n");
		os.write("        }\n");
		os.write("      }\n");
		os.write("    }\n");
		os.write("  }\n");
		os.write("  return &min_now;\n");
		os.write("}\n\n");
	}

	private static void writeSymHash(LazySpinChecker repGenerator,
			OutputStreamWriter os) throws IOException {
		os.write("int sym_hash(State* s)\n");
		os.write("{\n");
		os.write("  #ifndef SYM_HASH_PRIME\n");
		os.write("  #define SYM_HASH_PRIME 23\n");
		os.write("  #endif\n");
		os.write("  int result = 0;\n\n");
		
		List<List<InsensitiveVariableReference>> insensitiveVarReferences = new ArrayList<List<InsensitiveVariableReference>>();
		
		os.write("  /* Contribution from insensitive local variables */\n");
		
		for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++) {
			insensitiveVarReferences.add(repGenerator.insensitiveVariableReferencesForProcess(i, "s"));
		}
		
		for(int ref = 0; ref < insensitiveVarReferences.get(0).size(); ref++) {
		
			assert(!(insensitiveVarReferences.get(0).get(ref).getType() instanceof PidType || insensitiveVarReferences.get(0).get(ref).getType() instanceof ChanType));
			os.write("  result += ");
			for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++)	{
				if(i > 0) {
					os.write(" + ");
				}
				os.write("(" + insensitiveVarReferences.get(i).get(ref) + ")");
			}
			os.write(";\n");
			os.write("  result *= SYM_HASH_PRIME;\n");
		}

		Map<String, EnvEntry> globalVariables = repGenerator.getGlobalVariables();

		List<List<InsensitiveVariableReference>> insensitiveGlobalPidIndexedArrayElements = new ArrayList<List<InsensitiveVariableReference>>();
		for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++) {
			insensitiveGlobalPidIndexedArrayElements.add(new ArrayList<InsensitiveVariableReference>());
		}

		os.write("\n");
		os.write("  /* Contribution from global pid-indexed arrays (which are essentially local variables) */\n");
		for(String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if(entry instanceof VarEntry && !((VarEntry)entry).isHidden() && ((VarEntry)entry).getType() instanceof ArrayType &&
					PidType.isPid((VisibleType)((ArrayType)(((VarEntry)entry).getType())).getIndexType())) {
				for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++) {
					String prefix = "s->" + name + "[" + i + "]";
					insensitiveGlobalPidIndexedArrayElements.get(i).addAll(InsensitiveVariableReference.getInsensitiveVariableReferences("", ((ArrayType)((VarEntry)entry).getType()).getElementType(), prefix, repGenerator));
				}
			}
		}
		
		for(int ref = 0; ref < insensitiveGlobalPidIndexedArrayElements.get(0).size(); ref++) {
			os.write("  result += ");
			for(int i = 0; i < LazySpinChecker.numberOfRunningProcesses(); i++) {
				if(i > 0) {
					os.write(" + ");
				}
				os.write("(" + insensitiveGlobalPidIndexedArrayElements.get(i).get(ref) + ")");
			}
			os.write(";\n");
			os.write("  result *= SYM_HASH_PRIME;\n");
		}
		
		os.write("\n");
		os.write("  /* Contribution from insensitive globals */\n");

		String referencePrefix = "s->";
		List<InsensitiveVariableReference> insensitiveGlobals = new ArrayList<InsensitiveVariableReference>();

		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if(entry instanceof VarEntry && !((VarEntry)entry).isHidden()) {	
				insensitiveGlobals.addAll(InsensitiveVariableReference.getInsensitiveVariableReferences(name, ((VarEntry)entry).getType(), referencePrefix, repGenerator));
			}
		}
		
		for(InsensitiveVariableReference ref : insensitiveGlobals) {
			os.write("  result += (" + ref + ");\n");
			os.write("  result *= SYM_HASH_PRIME;\n");
		}
			
		os.write("\n");
		os.write("  return result;\n");
		os.write("}\n\n");
	}

	private static void writeSameCell(OutputStreamWriter os) throws IOException {
		os.write("int same_cell(State* s, int i, int j)\n");
		os.write("{\n");
		os.write("  return part_same_cell(s->_prt, i, j);\n");
		os.write("}\n\n");
	}

}
