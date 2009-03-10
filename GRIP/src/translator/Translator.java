package src.translator;


import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import src.exceptions.BadlyFormedGuardException;
import src.exceptions.BadlyInitialisedVariableException;
import src.exceptions.IllegalLocalAssignmentException;
import src.symmetricprism.analysis.DepthFirstAdapter;
import src.symmetricprism.node.AAssociatedProbability;
import src.symmetricprism.node.AAtomicAssignment;
import src.symmetricprism.node.AAtomicFactor;
import src.symmetricprism.node.ABoundeduntilPathprop;
import src.symmetricprism.node.ACommaArithmeticExpr;
import src.symmetricprism.node.ACompoundAndExpr;
import src.symmetricprism.node.ACompoundNotExpr;
import src.symmetricprism.node.ACompoundOrExpr;
import src.symmetricprism.node.AConstantDeclaration;
import src.symmetricprism.node.ADecimalProbability;
import src.symmetricprism.node.ADivMultDivExpr;
import src.symmetricprism.node.ADtmcType;
import src.symmetricprism.node.AEqualsAtomicFactor;
import src.symmetricprism.node.AEqualsRangeAtomicFactor;
import src.symmetricprism.node.AExpressionProbability;
import src.symmetricprism.node.AGlobalVariable;
import src.symmetricprism.node.AGtAtomicFactor;
import src.symmetricprism.node.AGteAtomicFactor;
import src.symmetricprism.node.AIdentifierRenaming;
import src.symmetricprism.node.AInitialisation;
import src.symmetricprism.node.ALeadingImplication;
import src.symmetricprism.node.ALtAtomicFactor;
import src.symmetricprism.node.ALteAtomicFactor;
import src.symmetricprism.node.AManyAssignment;
import src.symmetricprism.node.AManyIdentifierRenamings;
import src.symmetricprism.node.AManyStochasticUpdate;
import src.symmetricprism.node.AMaxArithmeticFactor;
import src.symmetricprism.node.AMdpType;
import src.symmetricprism.node.AMinArithmeticFactor;
import src.symmetricprism.node.AMinusArithmeticExpr;
import src.symmetricprism.node.AModule;
import src.symmetricprism.node.AMultMultDivExpr;
import src.symmetricprism.node.ANameArithmeticFactor;
import src.symmetricprism.node.ANequalsAtomicFactor;
import src.symmetricprism.node.ANequalsRangeAtomicFactor;
import src.symmetricprism.node.ANextPathprop;
import src.symmetricprism.node.ANondeterministicType;
import src.symmetricprism.node.ANumberArithmeticFactor;
import src.symmetricprism.node.AOneAssignment;
import src.symmetricprism.node.AOneIdentifierRenamings;
import src.symmetricprism.node.AOneStochasticUpdate;
import src.symmetricprism.node.AParentheseArithmeticFactor;
import src.symmetricprism.node.AParenthesisFactor;
import src.symmetricprism.node.APlusArithmeticExpr;
import src.symmetricprism.node.AProbabilisticPctlBody;
import src.symmetricprism.node.AProbabilisticType;
import src.symmetricprism.node.APropertiesSpec;
import src.symmetricprism.node.ARenaming;
import src.symmetricprism.node.ASimpleAndExpr;
import src.symmetricprism.node.ASimpleArithmeticExpr;
import src.symmetricprism.node.ASimpleMultDivExpr;
import src.symmetricprism.node.ASimpleNotExpr;
import src.symmetricprism.node.ASimpleOrExpr;
import src.symmetricprism.node.ASpecSpec;
import src.symmetricprism.node.AStatement;
import src.symmetricprism.node.ASteadyStatePctlBody;
import src.symmetricprism.node.ATrueAtomicFactor;
import src.symmetricprism.node.AUntilPathprop;
import src.symmetricprism.node.AUpdate;
import src.symmetricprism.node.AVariable;
import src.symmetricprism.node.Node;
import src.symmetricprism.node.PAndExpr;
import src.symmetricprism.node.PArithmeticExpr;
import src.symmetricprism.node.PArithmeticFactor;
import src.symmetricprism.node.PAssignment;
import src.symmetricprism.node.PAtomicFactor;
import src.symmetricprism.node.PCommaArithmeticExpr;
import src.symmetricprism.node.PConstantDeclaration;
import src.symmetricprism.node.PFactor;
import src.symmetricprism.node.PGlobalVariable;
import src.symmetricprism.node.PIdentifierRenamings;
import src.symmetricprism.node.PModule;
import src.symmetricprism.node.PMultDivExpr;
import src.symmetricprism.node.PNotExpr;
import src.symmetricprism.node.POrExpr;
import src.symmetricprism.node.PPctl;
import src.symmetricprism.node.PRenaming;
import src.symmetricprism.node.PStatement;
import src.symmetricprism.node.PStochasticUpdate;
import src.symmetricprism.node.PVariable;
import src.symmetricprism.node.TImplies;
import src.symmetricprism.node.TName;
import src.utilities.StringHelper;

public class Translator extends DepthFirstAdapter {

	private FileWriter fw;

	private String filename;

	private ModelType modelType;

	private int noSymmetricModules;

	private VariableSet variables;

	private Map<String, List<AStatement>> synchronisationStatements;

	private Map<AStatement,List<List<Integer>>> localStatesForSynchronisationStatements;
	
	private List<String> masterSlaveSynchronisationActions;
	
	private String symmetricModuleName;

	private boolean eliminate;
	
	private String formulaRHS = null;
	
	public Translator(String filename, boolean optimise, boolean eliminate) {
		this.filename = filename;
		this.eliminate = eliminate;
		variables = new VariableSet(optimise);
		synchronisationStatements = new HashMap<String, List<AStatement>>();
		masterSlaveSynchronisationActions = new ArrayList<String>();
		try {
			fw = new FileWriter(filename);
		} catch (IOException e) {
			reportFileError(e);
		}
	}

	private void reportFileError(IOException e) {
		System.out.println("Error writing to " + this.filename);
		e.printStackTrace();
		System.exit(1);
	}

	public void caseASpecSpec(ASpecSpec node) {
		modelType = ((node.getType() instanceof ANondeterministicType) || (node.getType() instanceof AMdpType)) ? ModelType.nondeterministic
				: ( (node.getType() instanceof AProbabilisticType) || (node.getType() instanceof ADtmcType)) ? ModelType.probabilistic : ModelType.stochastic ;
		symmetricModuleName = Helper.extractName(((AModule)(node.getModule().get(node.getModule().size()-1))).getName());

		if (Helper
				.extractNumber(((AModule)(node.getModule().get(node.getModule().size()-1))).getName())!=1) {
			System.out.println("The symmetric module should be named " + symmetricModuleName
					+ "1");
			System.exit(0);
		}

		try {
			fw.write(modelType + "\n\n");

			extractGlobalVariables(node.getGlobalVariable());

			extractNonSymmetricModuleVariables(node.getModule());
		
			extractLocalVariables(((AModule)node.getModule().get(node.getModule().size()-1)).getVariable());

			extractMasterSlaveSynchronisationStatements(((AModule)node.getModule().get(node.getModule().size()-1)).getStatement());
			
			handleRenamings(node.getRenaming());

			for(int i=0; i<node.getModule().size()-1; i++) {
				handleNonSymmetricModule((AModule)node.getModule().get(i));
			}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		handleSymmetricModule((AModule)node.getModule().get(node.getModule().size()-1));

	}

	private void extractMasterSlaveSynchronisationStatements(LinkedList<PStatement> statements) {
		for(PStatement statement : statements) {
			TName action = ((AStatement)statement).getName();
			if(action!=null && Helper.extractNumber(action)==1) {
				masterSlaveSynchronisationActions.add(Helper.extractName(action));
			}
		}
	}

	private void handleNonSymmetricModule(AModule module) throws IOException {
		fw.write(module.getModuletok().getText() + " " + module.getName().getText() + "\n\n");
		for(PVariable variable : module.getVariable()) {
			fw.write("  " + variable + "\n");
		}
		fw.write("\n");
		
		for(int i=0; i<module.getStatement().size(); i++) {
			AStatement statement = (AStatement)module.getStatement().get(i);
			fw.write("  [");
			if(statement.getName() != null) {
				if(Helper.extractNumber(statement.getName())==0) {
					fw.write(statement.getName().getText());
				} else if(Helper.extractNumber(statement.getName())==1) {
					fw.write(Helper.extractName(statement.getName()));
					for(int j=1; j<noSymmetricModules; j++) {
						AStatement symmetricStatement = (AStatement)module.getStatement().get(i+j);
						if(!matchingSymmetricStatement(statement,symmetricStatement,j+1)) {
							System.out.println("Error: asymmetric synchronisation action at line " + statement.getName().getLine());
							System.exit(0);
						}
					}
					i += noSymmetricModules-1;
					
				} else {
					System.out.println("Error: asymmetric synchronisation action at line " + statement.getName().getLine());
					System.exit(0);
				}
				
			}
			fw.write("] " + translateSymmetricGuard(statement.getOrExpr(),true) + " -> " + StringHelper.removeWhitespace(statement.getStochasticUpdate().toString()) + ";\n");
			
		}

		fw.write(module.getEndmodule().getText() + "\n\n");
	}

	private String translateSymmetricGuard(POrExpr orExpr, boolean allowAsymmetric) {
		// TODO this isn't really a satisfactory solution
		try {
			return translateOrExprWithAssignment(orExpr,new ArrayList<Integer>(),new HashMap<String,Integer>(),allowAsymmetric);
		} catch (BadlyFormedGuardException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	private boolean matchingSymmetricStatement(AStatement statement, AStatement symmetricStatement, int i) {
		return symmetricStatement.getName()!=null && Helper.extractName(symmetricStatement.getName()).equals(Helper.extractName(statement.getName()))
		&& Helper.extractNumber(symmetricStatement.getName())==i && (statement.getOrExpr().toString()+statement.getRightarrow().toString() + statement.getStochasticUpdate().toString() + statement.getSemicolon().toString()).equals(symmetricStatement.getOrExpr().toString()+symmetricStatement.getRightarrow().toString() + symmetricStatement.getStochasticUpdate().toString() + symmetricStatement.getSemicolon().toString());
	}

	private void extractNonSymmetricModuleVariables(LinkedList<PModule> modules) {
		for(int i=0; i<modules.size()-1; i++) {
			for(PVariable variable : ((AModule)modules.get(i)).getVariable()) {
				variables.addGlobal((AVariable)variable);
			}
		}
	}

	private void extractGlobalVariables(
			LinkedList<PGlobalVariable> globalVariable) {
		for (PGlobalVariable o : globalVariable) {

			try {
				fw.write(o.toString() + "\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			variables.addGlobal((AVariable) ((AGlobalVariable) o).getVariable());
		}

		try {
			fw.write("\n");
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	private void extractLocalVariables(List<PVariable> variable) {
		for (PVariable o : variable) {

			AVariable var = (AVariable) o;

			try {
				String name = Helper.extractName(var.getName());
				int moduleNumber = Helper.extractNumber(var.getName());
				int lower = Helper.toInt(var.getLow().getText());
				int upper = Helper.toInt(var.getHigh().getText());
				int start = (var.getInitialisation() != null ? Helper
						.toInt(((AInitialisation) var.getInitialisation())
								.getNumber().getText()) : lower);

				if (moduleNumber != 1) {
					System.out
							.println("Local variables of module 1 must end with 1");
					System.exit(0);
				}

				if (!variables
						.putLocal(name, new VarEntry(lower, upper, start))) {
					System.out.println("Duplicate local variable name");
					System.exit(0);
				}

			} catch (BadlyInitialisedVariableException e) {
				System.out.println(e);
				System.exit(0);
			}
		}

	}

	private void handleRenamings(LinkedList<PRenaming> renamings) {
		noSymmetricModules = renamings.size() + 1;
		int i = 2;
		for (PRenaming o : renamings) {
			ARenaming renaming = (ARenaming) o;

			if (!wellFormedRenaming(i, renaming)) {
				System.out.println("Module " + i
						+ " should have the form: module <name>" + i
						+ " = <name>1 [<var>1=<var>" + i + ", <var>" + i
						+ "=<var>1, ... ] endmodule");
				System.exit(0);
			}

			i++;
		}

	}

	private boolean wellFormedRenaming(int i, ARenaming module) {

		if (!(module.getProcess1().getText().equals(symmetricModuleName + 1) && module
				.getProcessi().getText().equals(symmetricModuleName + i))) {
			return false;
		}

		PIdentifierRenamings renamingList = module.getIdentifierRenamings();

		int noRenamings = size(renamingList);

		if(noRenamings != 2*variables.getLocalVariableNames().size() + masterSlaveSynchronisationActions.size()) {
			return false;
		}
		
		for (int j=0; j<variables.getLocalVariableNames().size(); j++) {

			AIdentifierRenaming firstRenaming = (AIdentifierRenaming)((AManyIdentifierRenamings)renamingList).getIdentifierRenaming();

			AIdentifierRenaming secondRenaming;
			
			renamingList = ((AManyIdentifierRenamings)renamingList).getIdentifierRenamings();
			
			if(renamingList instanceof AOneIdentifierRenamings) {
				secondRenaming = (AIdentifierRenaming)((AOneIdentifierRenamings)renamingList).getIdentifierRenaming();
			} else {
				secondRenaming = (AIdentifierRenaming)((AManyIdentifierRenamings)renamingList).getIdentifierRenaming();
			}

			String var = variables.getLocalVariableNames().get(j);
			
			if(!(firstRenaming.getLeft().getText().equals(var+1)&&firstRenaming.getRight().getText().equals(var+i)
					&& secondRenaming.getLeft().getText().equals(var+i)&&secondRenaming.getRight().getText().equals(var+1))) {
				return false;
			}
			
			if(renamingList instanceof AOneIdentifierRenamings) {
				return j==variables.getLocalVariableNames().size()-1 && masterSlaveSynchronisationActions.isEmpty();
			}
			
			renamingList = ((AManyIdentifierRenamings)renamingList).getIdentifierRenamings();
		}

		for (String action : masterSlaveSynchronisationActions) {

			AIdentifierRenaming renaming;
			
			if(renamingList instanceof AManyIdentifierRenamings) {
				renaming = (AIdentifierRenaming)((AManyIdentifierRenamings)renamingList).getIdentifierRenaming();
				renamingList = ((AManyIdentifierRenamings)renamingList).getIdentifierRenamings();
			} else {
				renaming = (AIdentifierRenaming)((AOneIdentifierRenamings)renamingList).getIdentifierRenaming();
			}
			
			if(!(renaming.getLeft().getText().equals(action+1) && renaming.getRight().getText().equals(action+i))) {
				return false;
			}
		}
		
		return true;
	}

	private int size(PIdentifierRenamings renamingList) {
		int result = 1;
		for(; renamingList instanceof AManyIdentifierRenamings; result++) {
			renamingList = ((AManyIdentifierRenamings)renamingList).getIdentifierRenamings();
		}
		return result;
	}

	public void handleSymmetricModule(AModule module) {
		try {

			if (eliminate) {
				writeFormula();
			}

			fw.write("module generic_process\n");

			writeCounterVariables();
			
			translateBasicStatements(module.getStatement());
			
			fw.write("\nendmodule\n");

			fw.close();
		} catch (IOException e) {
			reportFileError(e);
		}

	}

	private void writeFormula() throws IOException {
		fw.write("formula no_" + (variables.allAssignments().size() - 1) + " = ");
		
		formulaRHS = "(" + noSymmetricModules + "-(";
		for (int i = 0; i < variables.allAssignments().size() - 1; i++) {
			formulaRHS += "no_" + i;
			if (i < variables.allAssignments().size() - 2) {
				formulaRHS += "+";
			}
		}
		formulaRHS += "))";
		
		fw.write(formulaRHS + documentLocalState(variables.allAssignments().get(
						variables.allAssignments().size() - 1)) + "\n");
	}

	private void writeCounterVariables() throws IOException {

		List<List<Integer>> localStates = variables.allAssignments();

		for (int i = 0; i < (eliminate ? localStates.size() - 1 : localStates
				.size()); i++) {
			try {
				fw.write(" no_" + variables.abstractValue(localStates.get(i))
						+ " : [0.." + noSymmetricModules + "] init ");
				if (localStates.get(i).equals(variables.getInitialAssignment())) {
					fw.write(String.valueOf(noSymmetricModules));
				} else {
					fw.write("0");
				}
				fw.write(documentLocalState(localStates.get(i)));
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
		}
		fw.write("\n");

	}

	private String documentLocalState(List<Integer> localState) {
		String result = ";    // No modules in state (";
		for (int i = 0; i < localState.size(); i++) {
			result += String.valueOf(localState.get(i));
			if (i < localState.size() - 1) {
				result += ",";
			}
		}
		return result + ")\n";
	}

	private void translateBasicStatements(List<PStatement> statements) {

		for (PStatement pStatement : statements) {

			AStatement statement = (AStatement) pStatement;

			PAndExpr globalGuard = null;
			Set<List<Integer>> localStatesInWhichLocalGuardHolds;

			if(statement.getOrExpr() instanceof ASimpleOrExpr &&
					((ASimpleOrExpr)statement.getOrExpr()).getAndExpr() instanceof ACompoundAndExpr) {
				globalGuard = ((ACompoundAndExpr)((ASimpleOrExpr)statement.getOrExpr()).getAndExpr()).getAndExpr();

				localStatesInWhichLocalGuardHolds = variables.satisfies(((ACompoundAndExpr)((ASimpleOrExpr)statement.getOrExpr()).getAndExpr()).getNotExpr(),1);
			
			} else {
				localStatesInWhichLocalGuardHolds = variables.satisfies(statement.getOrExpr(), 1);
			}

			List<List<Integer>> listOfLocalStates = new ArrayList<List<Integer>>();
			listOfLocalStates.addAll(localStatesInWhichLocalGuardHolds);
			Collections.sort(listOfLocalStates, new LocalStateComparator());

			if (statement.getName() != null	&& Helper.extractNumber(statement.getName()) == 0) {
				String action = Helper.extractName(statement.getName());
				if(synchronisationStatements.containsKey(action)) {
					synchronisationStatements.get(action).add(statement);
				} else {
					ArrayList<AStatement> statementList = new ArrayList<AStatement>();
					statementList.add(statement);
					synchronisationStatements.put(action,statementList);
				}
				
				localStatesForSynchronisationStatements.put(statement,listOfLocalStates);
				
			} else {
				
				String action = "";
				
				if(statement.getName()!=null) {
					action = Helper.extractName(statement.getName());
				}

				List<String> relevantGlobalVariables = variables.globalsUsedToUpdateLocals(statement
						.getStochasticUpdate());

				List<Map<String, Integer>> valuations = variables
						.valuationsOfGlobals(relevantGlobalVariables);
								
				for (Map<String, Integer> valuation : valuations) {

					for (List<Integer> localState : listOfLocalStates) {

						String reducedGlobalGuard = "";
	
						for (Iterator<String> iter = valuation.keySet()
								.iterator(); iter.hasNext();) {
							String globalName = iter.next();
							reducedGlobalGuard += " & (" + globalName + "="
									+ valuation.get(globalName) + ")";
						}
	
						if (globalGuard != null) {
							reducedGlobalGuard += " & "
									+ translateSymmetricGuardWithAssignment(globalGuard,localState,valuation,true);
						}
	
						String reducedUpdate = translateUpdate(statement
								.getStochasticUpdate(), localState, valuation);
						
						try {
							if (modelType == ModelType.probabilistic) {
								for (int i = 0; i < noSymmetricModules; i++) {
									fw.write("  [" + action + "] (no_"
											+ variables
													.abstractValue(localState)
											+ ">" + i + ")"
											+ reducedGlobalGuard + " -> "
											+ reducedUpdate + ";\n");
								}
							} else {
								fw.write("  [" + action + "] (no_"
										+ variables.abstractValue(localState)
										+ ">0)"
										+ reducedGlobalGuard + " -> "
										+ reducedUpdate + ";\n");
							}
						} catch (IOException e) {
							reportFileError(e);
						} catch (IllegalLocalAssignmentException e) {
							// Unreachable
						}
					}
				}
			}
		}
	}

	/** ***************************************************** */
	/* Methods to translate global guards into generic form */
	/** ***************************************************** */

	private String partiallyEvaluate(PArithmeticExpr arithmeticExpr,
			List<Integer> assignment, Map<String, Integer> valuation) {

		if (refersOnlyTo(1, valuation.keySet(), arithmeticExpr) && doesNotInvolveDivision(arithmeticExpr)) {
			return String.valueOf(variables.evaluate(arithmeticExpr,
					assignment, valuation, 1));
		}
		if (arithmeticExpr instanceof ASimpleArithmeticExpr) {
			return partiallyEvaluate(((ASimpleArithmeticExpr) arithmeticExpr)
					.getMultDivExpr(), assignment,valuation);
		}
		if (arithmeticExpr instanceof APlusArithmeticExpr) {
			
			if(isSymmetricSummation((APlusArithmeticExpr)arithmeticExpr)) {
				return genericFormOfSymmetricSummation((APlusArithmeticExpr)arithmeticExpr);
			}
			if(isAsymmetricSummation((APlusArithmeticExpr)arithmeticExpr)) {
				return genericFormOfAsymmetricSummation((APlusArithmeticExpr)arithmeticExpr,assignment);
			}
			
			return partiallyEvaluate(((APlusArithmeticExpr) arithmeticExpr)
					.getArithmeticExpr(), assignment,valuation)
					+ "+"
					+ partiallyEvaluate(((APlusArithmeticExpr) arithmeticExpr)
							.getMultDivExpr(), assignment,valuation);
		}
		return partiallyEvaluate(((AMinusArithmeticExpr) arithmeticExpr)
				.getArithmeticExpr(), assignment,valuation)
				+ "-"
				+ partiallyEvaluate(((AMinusArithmeticExpr) arithmeticExpr)
						.getMultDivExpr(), assignment,valuation);
	}

	private boolean doesNotInvolveDivision(PArithmeticExpr arithmeticExpr) {
		if(arithmeticExpr instanceof ASimpleArithmeticExpr) {
			return doesNotInvolveDivision(((ASimpleArithmeticExpr)arithmeticExpr).getMultDivExpr());
		}
		if(arithmeticExpr instanceof APlusArithmeticExpr) {
			return doesNotInvolveDivision(((APlusArithmeticExpr)arithmeticExpr).getArithmeticExpr()) && doesNotInvolveDivision(((APlusArithmeticExpr)arithmeticExpr).getMultDivExpr());
		}
		return doesNotInvolveDivision(((AMinusArithmeticExpr)arithmeticExpr).getArithmeticExpr()) && doesNotInvolveDivision(((AMinusArithmeticExpr)arithmeticExpr).getMultDivExpr());

	}

	private String partiallyEvaluate(PMultDivExpr multDivExpr,
			List<Integer> assignment,Map<String,Integer> valuation) {
		if (refersOnlyTo(1, valuation.keySet(), multDivExpr) && doesNotInvolveDivision(multDivExpr)) {
			return String.valueOf(variables.evaluate(multDivExpr, assignment, valuation, 1));
		}
		if (multDivExpr instanceof ASimpleMultDivExpr) {
			return partiallyEvaluate(((ASimpleMultDivExpr) multDivExpr)
					.getArithmeticFactor(), assignment, valuation);
		}
		if (multDivExpr instanceof AMultMultDivExpr) {

			if(isSymmetricProduct((AMultMultDivExpr)multDivExpr)) {
				return genericFormOfSymmetricProduct((AMultMultDivExpr)multDivExpr);
			}
			if(isAsymmetricProduct((AMultMultDivExpr)multDivExpr)) {
				return genericFormOfAsymmetricProduct((AMultMultDivExpr)multDivExpr,assignment);
			}
			
			return partiallyEvaluate(((AMultMultDivExpr) multDivExpr)
					.getMultDivExpr(), assignment, valuation) + "*" +
					partiallyEvaluate(((AMultMultDivExpr) multDivExpr)
					.getArithmeticFactor(), assignment, valuation);
		}
		return partiallyEvaluate(((ADivMultDivExpr) multDivExpr)
				.getArithmeticFactor(), assignment, valuation)
				+ "/"
				+ partiallyEvaluate(((ADivMultDivExpr) multDivExpr)
						.getMultDivExpr(), assignment,valuation);
	}

	private boolean doesNotInvolveDivision(PMultDivExpr multDivExpr) {
		if(multDivExpr instanceof ASimpleMultDivExpr) {
			return doesNotInvolveDivision(((ASimpleMultDivExpr)multDivExpr).getArithmeticFactor());
		}
		if(multDivExpr instanceof AMultMultDivExpr) {
			return doesNotInvolveDivision(((AMultMultDivExpr)multDivExpr).getArithmeticFactor()) && doesNotInvolveDivision(((AMultMultDivExpr)multDivExpr).getMultDivExpr());
		}
		return false;
	}

	private String partiallyEvaluate(PArithmeticFactor arithmeticFactor,
			List<Integer> assignment, Map<String,Integer> valuation) {
		if (refersOnlyTo(1, valuation.keySet(), arithmeticFactor) && doesNotInvolveDivision(arithmeticFactor)) {
			return String.valueOf(variables.evaluate(arithmeticFactor,
					assignment, valuation, 1));
		}
		if (arithmeticFactor instanceof AParentheseArithmeticFactor) {
			return "("
					+ partiallyEvaluate(
							((AParentheseArithmeticFactor) arithmeticFactor)
									.getArithmeticExpr(), assignment,valuation) + ")";
		}
		if (arithmeticFactor instanceof AMinArithmeticFactor) {
			String result = "min("
					+ partiallyEvaluate(
							((AMinArithmeticFactor) arithmeticFactor)
									.getArithmeticExpr(), assignment,valuation);
			for (PCommaArithmeticExpr o : ((AMinArithmeticFactor) arithmeticFactor)
					.getCommaArithmeticExpr()) {
				result += ","
						+ partiallyEvaluate(((ACommaArithmeticExpr) o)
								.getArithmeticExpr(), assignment,valuation);
			}
			return result += ")";
		}
		if (arithmeticFactor instanceof AMaxArithmeticFactor) {
			String result = "max("
					+ partiallyEvaluate(
							((AMaxArithmeticFactor) arithmeticFactor)
									.getArithmeticExpr(), assignment,valuation);
			for (PCommaArithmeticExpr o : ((AMaxArithmeticFactor) arithmeticFactor)
					.getCommaArithmeticExpr()) {
				result += ","
						+ partiallyEvaluate(((ACommaArithmeticExpr) o)
								.getArithmeticExpr(), assignment,valuation);
			}
			return result += ")";
		}
		
		if(arithmeticFactor instanceof ANameArithmeticFactor) {
			if(Helper.extractNumber(((ANameArithmeticFactor)arithmeticFactor).getName())>1) {
				System.out.println("Error: variable " + ((ANameArithmeticFactor)arithmeticFactor).getName().getText() + " used illegally at line " + ((ANameArithmeticFactor)arithmeticFactor).getName().getLine());
				System.exit(0);
			}
		}
		
		return StringHelper.removeWhitespace(arithmeticFactor.toString());
	}

	private boolean doesNotInvolveDivision(PArithmeticFactor arithmeticFactor) {
		if(arithmeticFactor instanceof ANumberArithmeticFactor || arithmeticFactor instanceof ANameArithmeticFactor) {
			return true;
		}
		if (arithmeticFactor instanceof AParentheseArithmeticFactor) {
			doesNotInvolveDivision(((AParentheseArithmeticFactor) arithmeticFactor).getArithmeticExpr());
		}
		if (arithmeticFactor instanceof AMinArithmeticFactor) {
			if(!doesNotInvolveDivision(((AMinArithmeticFactor) arithmeticFactor)
									.getArithmeticExpr())) {
				return false;
			}
			for (PCommaArithmeticExpr o : ((AMinArithmeticFactor) arithmeticFactor)
					.getCommaArithmeticExpr()) {
				if(!doesNotInvolveDivision(((ACommaArithmeticExpr)o).getArithmeticExpr())) {
					return false;
				}
			}
			return true;
		}

		if(!doesNotInvolveDivision(((AMaxArithmeticFactor) arithmeticFactor)
				.getArithmeticExpr())) {
			return false;
		}
		for (PCommaArithmeticExpr o : ((AMaxArithmeticFactor) arithmeticFactor).getCommaArithmeticExpr()) {
			if(!doesNotInvolveDivision(((ACommaArithmeticExpr)o).getArithmeticExpr())) {
				return false;
			}
		}
		return true;
	}

	private String translateSymmetricGuardWithAssignment(PAndExpr guard,
			List<Integer> localState, Map<String,Integer> valuation, boolean allowAsymmetric) {

		String result = null;
		try {
			result = translateAndExprWithAssignment(guard, localState,valuation,allowAsymmetric);
		} catch (BadlyFormedGuardException e) {
			System.out.println(e);
			System.out.println("   " + nodeString(guard));
			System.exit(0);
		}
		return result;
	}

	private String translateOrExprWithAssignment(POrExpr orExpr, List<Integer> localState,Map<String,Integer> valuation, boolean allowAsymmetric)
			throws BadlyFormedGuardException {
		if (orExpr instanceof ASimpleOrExpr) {
			return translateAndExprWithAssignment(((ASimpleOrExpr) orExpr).getAndExpr(),
					localState,valuation,allowAsymmetric);
		}

		if (refersOnlyTo(1, ((ACompoundOrExpr) orExpr).getAndExpr())) {

			if (!validOrGuard(StringHelper
					.removeWhitespace(((ACompoundOrExpr) orExpr).getAndExpr()
							.toString()), ((ACompoundOrExpr) orExpr)
					.getOrExpr(), 1)) {
				throw new BadlyFormedGuardException(orExpr,((ACompoundOrExpr)orExpr).getOr().getLine());
			}
			return genericFormOfSymmetricGuard((ACompoundOrExpr) orExpr);
		} else if (allowAsymmetric && refersOnlyTo(2, ((ACompoundOrExpr) orExpr).getAndExpr())) {

			if (!validOrGuard(StringHelper
					.removeWhitespace(((ACompoundOrExpr) orExpr).getAndExpr()
							.toString()), ((ACompoundOrExpr) orExpr)
					.getOrExpr(), 2)) {
				throw new BadlyFormedGuardException(orExpr,((ACompoundOrExpr)orExpr).getOr().getLine());
			}
			return genericFormOfAsymmetricGuard((ACompoundOrExpr) orExpr,
					localState);
		}

		return translateAndExprWithAssignment(((ACompoundOrExpr) orExpr).getAndExpr(),
				localState,valuation,allowAsymmetric)
				+ "|"
				+ translateOrExprWithAssignment(((ACompoundOrExpr) orExpr).getOrExpr(),
						localState,valuation,allowAsymmetric);
	}

	private boolean refersOnlyTo(int i, PAndExpr andExpr) {
		return refersOnlyTo(i, new HashSet<String>(), andExpr);
	}

	private boolean refersOnlyTo(int i, PNotExpr notExpr) {
		return refersOnlyTo(i, new HashSet<String>(), notExpr);
	}

	private boolean refersOnlyTo(int i, PMultDivExpr multDivExpr) {
		return refersOnlyTo(i,new HashSet<String>(),multDivExpr);
	}
	
	private boolean refersOnlyTo(int i, PArithmeticFactor arithmeticFactor) {
		return refersOnlyTo(i,new HashSet<String>(),arithmeticFactor);
	}

	
	private String translateAndExprWithAssignment(PAndExpr andExpr, List<Integer> localState, Map<String,Integer> valuation, boolean allowAsymmetric)
			throws BadlyFormedGuardException {
		if (andExpr instanceof ASimpleAndExpr) {
			return translateNotExprWithAssignment(((ASimpleAndExpr) andExpr).getNotExpr(),
					localState,valuation,allowAsymmetric);
		}

		if (refersOnlyTo(1, ((ACompoundAndExpr) andExpr).getNotExpr())) {

			if (!validAndGuard(StringHelper
					.removeWhitespace(((ACompoundAndExpr) andExpr).getNotExpr()
							.toString()), ((ACompoundAndExpr) andExpr)
					.getAndExpr(), 1)) {
				throw new BadlyFormedGuardException(andExpr,((ACompoundAndExpr)andExpr).getAnd().getLine());
			}
			return genericFormOfSymmetricGuard((ACompoundAndExpr) andExpr);
		} else if (allowAsymmetric && refersOnlyTo(2, ((ACompoundAndExpr) andExpr).getNotExpr())) {

			if (!validAndGuard(StringHelper
					.removeWhitespace(((ACompoundAndExpr) andExpr).getNotExpr()
							.toString()), ((ACompoundAndExpr) andExpr)
					.getAndExpr(), 2)) {
				throw new BadlyFormedGuardException(andExpr,((ACompoundAndExpr)andExpr).getAnd().getLine());
			}
			return genericFormOfAsymmetricGuard((ACompoundAndExpr) andExpr,
					localState);
		}

		return translateNotExprWithAssignment(((ACompoundAndExpr) andExpr).getNotExpr(),
				localState,valuation,allowAsymmetric)
				+ "&"
				+ translateAndExprWithAssignment(((ACompoundAndExpr) andExpr).getAndExpr(),
						localState,valuation,allowAsymmetric);
	}

	private String translateNotExprWithAssignment(PNotExpr notExpr, List<Integer> localState, Map<String,Integer> valuation, boolean allowAsymmetric)
			throws BadlyFormedGuardException {
		if (notExpr instanceof ASimpleNotExpr) {
			return translateFactorWithAssignment(((ASimpleNotExpr) notExpr).getFactor(),
					localState,valuation, allowAsymmetric);
		}

		return "!"
				+ translateFactorWithAssignment(((ACompoundNotExpr) notExpr).getFactor(),
						localState,valuation,allowAsymmetric);
	}

	private String translateFactorWithAssignment(PFactor factor, List<Integer> localState, Map<String,Integer> valuation, boolean allowAsymmetric)
			throws BadlyFormedGuardException {
		if (factor instanceof AParenthesisFactor) {
			return "("
					+ translateOrExprWithAssignment(
							((AParenthesisFactor) factor).getOrExpr(),
							localState,valuation,allowAsymmetric) + ")";
		}

		return translateAtomicFactorWithAssignment(((AAtomicFactor)factor).getAtomicFactor(),localState,valuation);
	}
	
	private String translateAtomicFactorWithAssignment(PAtomicFactor atomicFactor,
			List<Integer> assignment, Map<String,Integer> valuation) {
		
		if (atomicFactor instanceof AEqualsRangeAtomicFactor) {
			return partiallyEvaluate(((AEqualsRangeAtomicFactor) atomicFactor)
					.getArithmeticExpr(), assignment,valuation)
					+ "="
					+ StringHelper
							.removeWhitespace(((AEqualsRangeAtomicFactor) atomicFactor)
									.getRange().toString());
		} else if (atomicFactor instanceof ANequalsRangeAtomicFactor) {
			return partiallyEvaluate(((ANequalsRangeAtomicFactor) atomicFactor)
					.getArithmeticExpr(), assignment,valuation)
					+ "!="
					+ StringHelper
							.removeWhitespace(((ANequalsRangeAtomicFactor) atomicFactor)
									.getRange().toString());
		} else if (atomicFactor instanceof AEqualsAtomicFactor) {
			return partiallyEvaluate(((AEqualsAtomicFactor) atomicFactor)
					.getLeft(), assignment,valuation)
					+ "="
					+ partiallyEvaluate(((AEqualsAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof ANequalsAtomicFactor) {
			return partiallyEvaluate(((ANequalsAtomicFactor) atomicFactor)
					.getLeft(), assignment,valuation)
					+ "!="
					+ partiallyEvaluate(((ANequalsAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof ALtAtomicFactor) {
			return partiallyEvaluate(
					((ALtAtomicFactor) atomicFactor).getLeft(), assignment,valuation)
					+ "<"
					+ partiallyEvaluate(((ALtAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof ALteAtomicFactor) {
			return partiallyEvaluate(((ALteAtomicFactor) atomicFactor)
					.getLeft(), assignment,valuation)
					+ "<="
					+ partiallyEvaluate(((ALteAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof AGtAtomicFactor) {
			return partiallyEvaluate(
					((AGtAtomicFactor) atomicFactor).getLeft(), assignment,valuation)
					+ ">"
					+ partiallyEvaluate(((AGtAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof AGteAtomicFactor) {
			return partiallyEvaluate(((AGteAtomicFactor) atomicFactor).getLeft(),
					assignment,valuation)
					+ ">="
					+ partiallyEvaluate(((AGteAtomicFactor) atomicFactor)
							.getRight(), assignment,valuation);
		} else if (atomicFactor instanceof ATrueAtomicFactor) {
			return "true";
		}
		// Must be AFalseAtomicFactor
		return "false";
	}
	
	/** ************************************************************************* */
	/* Methods to check that an expression refers only to variables of module i */
	/** ************************************************************************* */

	private boolean refersOnlyTo(Integer value, Set<String> globals, PNotExpr notExpr) {
		if (notExpr instanceof ACompoundNotExpr) {
			return refersOnlyTo(value, globals, ((ACompoundNotExpr) notExpr)
					.getFactor());
		}
		return refersOnlyTo(value, globals, ((ASimpleNotExpr) notExpr).getFactor());
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, PFactor factor) {
		if (factor instanceof AParenthesisFactor) {
			return refersOnlyTo(value, globals, ((AParenthesisFactor) factor)
					.getOrExpr());
		}
		return refersOnlyTo(value, globals, ((AAtomicFactor) factor).getAtomicFactor());
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals,
			PAtomicFactor atomicFactor) {
		if (atomicFactor instanceof AEqualsAtomicFactor) {
			return refersOnlyTo(value, globals, (((AEqualsAtomicFactor) atomicFactor)
					.getLeft()))
					&& refersOnlyTo(value, globals,
							(((AEqualsAtomicFactor) atomicFactor).getRight()));
		}
		if (atomicFactor instanceof ANequalsAtomicFactor) {
			return refersOnlyTo(value, globals, (((ANequalsAtomicFactor) atomicFactor)
					.getLeft()))
					&& refersOnlyTo(value, globals,
							(((ANequalsAtomicFactor) atomicFactor).getRight()));
		}
		if (atomicFactor instanceof AEqualsRangeAtomicFactor) {
			return refersOnlyTo(value, globals,
					(((AEqualsRangeAtomicFactor) atomicFactor)
							.getArithmeticExpr()));
		}
		if (atomicFactor instanceof ANequalsRangeAtomicFactor) {
			return refersOnlyTo(value, globals,
					(((ANequalsRangeAtomicFactor) atomicFactor)
							.getArithmeticExpr()));
		}
		if (atomicFactor instanceof AGtAtomicFactor) {
			return refersOnlyTo(value, globals, (((AGtAtomicFactor) atomicFactor)
					.getLeft()))
					&& refersOnlyTo(value, globals, (((AGtAtomicFactor) atomicFactor)
							.getRight()));
		}
		if (atomicFactor instanceof AGteAtomicFactor) {
			return refersOnlyTo(value, globals, (((AGteAtomicFactor) atomicFactor)
					.getLeft()))
					&& refersOnlyTo(value, globals, (((AGteAtomicFactor) atomicFactor)
							.getRight()));
		}
		if (atomicFactor instanceof ALtAtomicFactor) {
			return refersOnlyTo(value, globals, (((ALtAtomicFactor) atomicFactor)
					.getLeft()))
					&& refersOnlyTo(value, globals, (((ALtAtomicFactor) atomicFactor)
							.getRight()));
		}
		return refersOnlyTo(value, globals, (((ALteAtomicFactor) atomicFactor)
				.getLeft()))
				&& refersOnlyTo(value, globals, (((ALteAtomicFactor) atomicFactor)
						.getRight()));
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, PArithmeticExpr expr) {
		if (expr instanceof ASimpleArithmeticExpr) {
			return refersOnlyTo(value, globals, (((ASimpleArithmeticExpr) expr)
					.getMultDivExpr()));
		}
		if (expr instanceof APlusArithmeticExpr) {
			return refersOnlyTo(value, globals, (((APlusArithmeticExpr) expr)
					.getArithmeticExpr()))
					&& refersOnlyTo(value, globals, (((APlusArithmeticExpr) expr)
							.getMultDivExpr()));
		}
		return refersOnlyTo(value, globals, (((AMinusArithmeticExpr) expr)
				.getArithmeticExpr()))
				&& refersOnlyTo(value, globals, (((AMinusArithmeticExpr) expr)
						.getMultDivExpr()));
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, PMultDivExpr expr) {
		if (expr instanceof ASimpleMultDivExpr) {
			return refersOnlyTo(value, globals, (((ASimpleMultDivExpr) expr)
					.getArithmeticFactor()));
		}
		if (expr instanceof AMultMultDivExpr) {
			return refersOnlyTo(value, globals, (((AMultMultDivExpr) expr)
					.getMultDivExpr()))
					&& refersOnlyTo(value, globals, (((AMultMultDivExpr) expr)
							.getArithmeticFactor()));
		}
		return refersOnlyTo(value, globals, (((ADivMultDivExpr) expr).getMultDivExpr()))
				&& refersOnlyTo(value, globals, (((ADivMultDivExpr) expr)
						.getArithmeticFactor()));
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, PArithmeticFactor factor) {
		if (factor instanceof AParentheseArithmeticFactor) {
			return refersOnlyTo(value, globals, (((AParentheseArithmeticFactor) factor)
					.getArithmeticExpr()));
		}
		if (factor instanceof ANumberArithmeticFactor) {
			return true;
		}
		if (factor instanceof AMinArithmeticFactor) {
			return refersOnlyTo(value, globals, ((AMinArithmeticFactor) factor)
					.getArithmeticExpr())
					&& refersOnlyTo(value, globals, ((AMinArithmeticFactor) factor)
							.getCommaArithmeticExpr());
		}
		if (factor instanceof AMaxArithmeticFactor) {
			return refersOnlyTo(value, globals, ((AMaxArithmeticFactor) factor)
					.getArithmeticExpr())
					&& refersOnlyTo(value, globals, ((AMaxArithmeticFactor) factor)
							.getCommaArithmeticExpr());
		}

		return value == Helper.extractNumber(((ANameArithmeticFactor) factor).getName()) ||	(Helper.extractNumber(((ANameArithmeticFactor)factor).getName())==0 && globals.contains(((ANameArithmeticFactor)factor).getName().getText()));
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, List<PCommaArithmeticExpr> list) {
		for (PCommaArithmeticExpr o : list) {
			if (!refersOnlyTo(value, globals, ((ACommaArithmeticExpr) o)
					.getArithmeticExpr())) {
				return false;
			}
		}
		return true;
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, POrExpr orExpr) {
		if (orExpr instanceof ASimpleOrExpr) {
			return refersOnlyTo(value, globals, ((ASimpleOrExpr) orExpr).getAndExpr());
		}
		return refersOnlyTo(value, globals, ((ACompoundOrExpr) orExpr).getAndExpr())
				& refersOnlyTo(value, globals, ((ACompoundOrExpr) orExpr).getOrExpr());
	}

	private boolean refersOnlyTo(Integer value, Set<String> globals, PAndExpr andExpr) {
		if (andExpr instanceof ASimpleAndExpr) {
			return refersOnlyTo(value, globals, ((ASimpleAndExpr) andExpr).getNotExpr());
		}
		return refersOnlyTo(value, globals, ((ACompoundAndExpr) andExpr).getNotExpr())
				&& refersOnlyTo(value, globals, ((ACompoundAndExpr) andExpr).getAndExpr());
	}

	/** ************************************************************************* */
	/*
	 * Methods to check whether a/symmetric guards are well formed. Given a
	 * string representation of he first operand in the con/disjunction they
	 * check that the rest matches
	 */
	/** *** */

	private boolean validOrGuard(String firstSubguard, POrExpr orExpr, int i) {

		for (int j = i + 1; j < noSymmetricModules; j++) {
			if (orExpr instanceof ASimpleOrExpr) {
				return false;
			}

			String currentSubguard = StringHelper
					.removeWhitespace(((ACompoundOrExpr) orExpr).getAndExpr()
							.toString());

			if (!firstSubguard.equals(substitute(i, j, currentSubguard))) {
				return false;
			}

			orExpr = ((ACompoundOrExpr) orExpr).getOrExpr();
		}

		if (orExpr instanceof ACompoundOrExpr) {
			return false;
		}

		String currentSubguard = StringHelper
				.removeWhitespace(((ASimpleOrExpr) orExpr).getAndExpr()
						.toString());

		return firstSubguard.equals(substitute(i, noSymmetricModules, currentSubguard));

	}

	private boolean validAndGuard(String firstSubguard, PAndExpr andExpr, int i) {

		for (int j = i + 1; j < noSymmetricModules; j++) {

			if (andExpr instanceof ASimpleAndExpr) {
				return false;
			}

			String currentSubguard = StringHelper
					.removeWhitespace(((ACompoundAndExpr) andExpr).getNotExpr()
							.toString());

			if (!firstSubguard.equals(substitute(i, j, currentSubguard))) {
				return false;
			}

			andExpr = ((ACompoundAndExpr) andExpr).getAndExpr();
		}

		if (andExpr instanceof ACompoundAndExpr) {
			return false;
		}

		String currentSubguard = StringHelper
				.removeWhitespace(((ASimpleAndExpr) andExpr).getNotExpr()
						.toString());

		return firstSubguard.equals(substitute(i, noSymmetricModules, currentSubguard));
	}

	private String substitute(int i, int j, String subguard) {
		// Replace j with i
		
		String result = new String(subguard);
		for (String var : variables.getLocalVariableNames()) {

			result = result.replace(var + j, var + i);

		}
		return result;
	}

	/** ****************************************************************** */
	/* Methods to convert a/symmetric guards and summations into their generic forms */
	/** ****************************************************************** */

	private boolean isSymmetricProduct(AMultMultDivExpr multExpr) {
		return refersOnlyTo(noSymmetricModules,multExpr.getArithmeticFactor()) && isSymmetricProductTail(multExpr.getMultDivExpr(),noSymmetricModules-1,StringHelper.removeWhitespace(multExpr.getArithmeticFactor().toString()));
	}

	private boolean isSymmetricProductTail(PMultDivExpr expr, int moduleNo, String exprString) {
		if(moduleNo==1) {
			return substitute(noSymmetricModules,1,StringHelper.removeWhitespace(expr.toString())).equals(exprString);
		}
		
		return expr instanceof AMultMultDivExpr && substitute(noSymmetricModules,moduleNo,StringHelper.removeWhitespace(((AMultMultDivExpr)expr).getArithmeticFactor().toString())).equals(exprString)
		   && isSymmetricProductTail(((AMultMultDivExpr)expr).getMultDivExpr(),moduleNo-1,exprString);		
	}

	private boolean isAsymmetricProduct(AMultMultDivExpr multExpr) {
		return refersOnlyTo(noSymmetricModules,multExpr.getArithmeticFactor()) && isAsymmetricProductTail(multExpr.getMultDivExpr(),noSymmetricModules-1,StringHelper.removeWhitespace(multExpr.getArithmeticFactor().toString()));
	}

	private boolean isAsymmetricProductTail(PMultDivExpr expr, int moduleNo, String exprString) {
		if(moduleNo==2) {
			return substitute(noSymmetricModules,2,StringHelper.removeWhitespace(expr.toString())).equals(exprString);
		}
		
		return expr instanceof AMultMultDivExpr && substitute(noSymmetricModules,moduleNo,StringHelper.removeWhitespace(((AMultMultDivExpr)expr).getArithmeticFactor().toString())).equals(exprString)
		   && isAsymmetricProductTail(((AMultMultDivExpr)expr).getMultDivExpr(),moduleNo-1,exprString);		
	}
	
	private boolean isSymmetricSummation(APlusArithmeticExpr plusExpr) {
		return refersOnlyTo(noSymmetricModules,plusExpr.getMultDivExpr()) && isSymmetricSummationTail(plusExpr.getArithmeticExpr(),noSymmetricModules-1,StringHelper.removeWhitespace(plusExpr.getMultDivExpr().toString()));
	}
	
	private boolean isSymmetricSummationTail(PArithmeticExpr expr, int moduleNo, String exprString) {
		if(moduleNo==1) {
			return substitute(noSymmetricModules,1,StringHelper.removeWhitespace(expr.toString())).equals(exprString);
		}
	
		return (expr instanceof APlusArithmeticExpr) && substitute(noSymmetricModules,moduleNo,StringHelper.removeWhitespace(((APlusArithmeticExpr)expr).getMultDivExpr().toString())).equals(exprString)
		   && isSymmetricSummationTail(((APlusArithmeticExpr)expr).getArithmeticExpr(),moduleNo-1,exprString);		
	}

	private boolean isAsymmetricSummation(APlusArithmeticExpr plusExpr) {
		return refersOnlyTo(noSymmetricModules,plusExpr.getMultDivExpr())&& isAsymmetricSummationTail(plusExpr.getArithmeticExpr(),noSymmetricModules-1,StringHelper.removeWhitespace(plusExpr.getMultDivExpr().toString()));
	}
	
	private boolean isAsymmetricSummationTail(PArithmeticExpr expr, int moduleNo, String exprString) {

		if(moduleNo==2) {
			return substitute(noSymmetricModules,2,StringHelper.removeWhitespace(expr.toString())).equals(exprString);
		}

		return expr instanceof APlusArithmeticExpr && substitute(noSymmetricModules,moduleNo,StringHelper.removeWhitespace(((APlusArithmeticExpr)expr).getMultDivExpr().toString())).equals(exprString)
		   && isAsymmetricSummationTail(((APlusArithmeticExpr)expr).getArithmeticExpr(),moduleNo-1,exprString);
	}
	
	private String genericFormOfSymmetricSummation(APlusArithmeticExpr plusExpr) {
		PMultDivExpr expr = plusExpr.getMultDivExpr();

		String result = "";
		
		for(int i=0; i<variables.allAssignments().size(); i++) {
			int evaluateFor_i= 0;
			try {
				evaluateFor_i = variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules);
				if(evaluateFor_i!=0) {
					result += "no_" + variables.abstractValue(variables.allAssignments().get(i));
					if(evaluateFor_i>1) {
						result += "*" + evaluateFor_i;
					}
				}
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
			if(evaluateFor_i>0 && i<variables.allAssignments().size()-1) {
				result += "+";
			}
		}

		if(result=="") {
			result = "0";
		}
		return result;
	}
	
	private String genericFormOfAsymmetricSummation(APlusArithmeticExpr plusExpr, List<Integer> localState) {
		PMultDivExpr expr = plusExpr.getMultDivExpr();

		String result = "";
		
		for(int i=0; i<variables.allAssignments().size(); i++) {
			try {
				if(variables.allAssignments().get(i).equals(localState)) {
					result += "(no_" + variables.abstractValue(variables.allAssignments().get(i)) + "-1)*" + variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules);
				} else {
					result += "no_" + variables.abstractValue(variables.allAssignments().get(i)) + "*" + variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules);
				}
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
			if(i<variables.allAssignments().size()-1) {
				result += "+";
			}
		}
		
		return result;
	}


	private String genericFormOfSymmetricProduct(AMultMultDivExpr multExpr) {
		PArithmeticFactor expr = multExpr.getArithmeticFactor();

		String result = "";
		
		for(int i=0; i<variables.allAssignments().size(); i++) {
			try {
				result += "func(pow," + variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules) + ",no_" + variables.abstractValue(variables.allAssignments().get(i)) + ")";
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
			if(i<variables.allAssignments().size()-1) {
				result += "*";
			}
		}
		
		return result;
	}

	
	private String genericFormOfAsymmetricProduct(AMultMultDivExpr multExpr, List<Integer> localState) {
		PArithmeticFactor expr = multExpr.getArithmeticFactor();

		String result = "";
		
		for(int i=0; i<variables.allAssignments().size(); i++) {
			try {
				if(variables.allAssignments().get(i).equals(localState)) {
					result += "func(pow," + variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules) + ",no_" + variables.abstractValue(variables.allAssignments().get(i)) + "-1)";
				} else {
					result += "func(pow," + variables.evaluate(expr,variables.allAssignments().get(i),new HashMap<String,Integer>(),noSymmetricModules) + ",no_" + variables.abstractValue(variables.allAssignments().get(i)) + ")";
				}
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
			if(i<variables.allAssignments().size()-1) {
				result += "*";
			}
		}
		
		return result;
	}


	
	
	private String genericFormOfAsymmetricGuard(ACompoundOrExpr orExpr,
			List<Integer> localState) {
		Set<List<Integer>> validStates = variables.satisfies(orExpr
				.getAndExpr(), 2);
		if (validStates.isEmpty()) {
			return "false";
		}

		String result = constructSummation(validStates);

		result += ">";
		return result += (validStates.contains(localState) ? "1" : "0");
	}

	private String genericFormOfAsymmetricGuard(ACompoundAndExpr andExpr,
			List<Integer> localState) {
		Set<List<Integer>> validStates = variables.satisfies(andExpr
				.getNotExpr(), 2);
		if (validStates.isEmpty()) {
			return "false";
		}
		String result = constructSummation(validStates);
		result += "=";
		return result += (validStates.contains(localState) ? noSymmetricModules
				: (noSymmetricModules - 1));
	}

	private String genericFormOfSymmetricGuard(ACompoundOrExpr orExpr) {
		Set<List<Integer>> validStates = variables.satisfies(orExpr
				.getAndExpr(), 1);
		if (validStates.isEmpty()) {
			return "false";
		}
		String result = constructSummation(validStates);
		return result += ">0";
	}

	private String genericFormOfSymmetricGuard(ACompoundAndExpr andExpr) {
		Set<List<Integer>> validStates = variables.satisfies(andExpr
				.getNotExpr(), 1);
		if (validStates.isEmpty()) {
			return "false";
		}
		String result = constructSummation(validStates);
		return result += "=" + noSymmetricModules;
	}

	/** **************************************** */
	/* Method to translate a stochastic update */
	/***************************************************************************
	 * @param valuation
	 **************************************************************************/

	private String translateUpdate(PStochasticUpdate stochasticUpdate,
			List<Integer> localState, Map<String, Integer> valuation) {
		List<String> updates = new ArrayList<String>();

		PStochasticUpdate update;
		for (update = stochasticUpdate; update instanceof AManyStochasticUpdate; update = ((AManyStochasticUpdate) update)
				.getStochasticUpdate()) {

			final AUpdate localUpdate = (AUpdate) ((AManyStochasticUpdate) update)
					.getUpdate();
			try {
				updates.add(processSingleUpdate(localUpdate, localState,
						valuation));
			} catch (IllegalLocalAssignmentException e) {
				// This means there is potential for a bad variable assignment,
				// but it will probably be unreachable
			}
		}

		final AUpdate localUpdate = (AUpdate) ((AOneStochasticUpdate) update)
				.getUpdate();
		try {
			updates
					.add(processSingleUpdate(localUpdate, localState, valuation));
		} catch (IllegalLocalAssignmentException e) {
			// This means there is potential for a bad variable assignment, but
			// it will probably be unreachable
		}

		String result = "";
		for (Iterator<String> iter = updates.iterator(); iter.hasNext();) {
			result += iter.next();
			if (iter.hasNext()) {
				result += " + ";
			}
		}
		return result;
	}

	/** *************** */
	/* Helper methods */
	/** *************** */

	private String processSingleUpdate(AUpdate localUpdate,
			List<Integer> oldState, Map<String, Integer> valuation)
			throws IllegalLocalAssignmentException {
		
		String probability = "";
		String update = "";
		
		if(modelType==ModelType.stochastic) {
			probability += "no_" + variables.abstractValue(oldState);
		}
		
		if (localUpdate.getAssociatedProbability() !=null) {
			if(modelType==ModelType.stochastic) {
				probability += "*";
			}
			
			if(((AAssociatedProbability)localUpdate.getAssociatedProbability()).getProbability() instanceof ADecimalProbability) {
				probability += nodeString(localUpdate.getAssociatedProbability());
			}
			else {
				probability += partiallyEvaluate(((AExpressionProbability)((AAssociatedProbability)localUpdate.getAssociatedProbability()).getProbability()).getArithmeticExpr(),oldState,valuation) + ":";
			}
		} else {
			if(modelType==ModelType.stochastic) {
				probability += ":";
			}
		}

		PAssignment assignments = localUpdate.getAssignment();

		List<Integer> newState = new ArrayList<Integer>(oldState);

		while (assignments instanceof AManyAssignment) {

			AAtomicAssignment assignment = (AAtomicAssignment) ((AManyAssignment) assignments)
					.getAtomicAssignment();

			if (Helper.extractNumber(assignment.getName()) == 0) {
				update += processGlobalAssignment(assignment, oldState,valuation);
			} else if (Helper.extractNumber(assignment.getName()) == 1) {
				processLocalAssignment(assignment, oldState, newState,
						valuation);
			} else {
				System.out
						.println("Error: update to local variable of another module at line "
								+ assignment.getName().getLine());
				System.exit(0);
			}
			assignments = ((AManyAssignment) assignments).getAssignment();
		}

		AAtomicAssignment assignment = (AAtomicAssignment) ((AOneAssignment) assignments)
				.getAtomicAssignment();

		if (Helper.extractNumber(assignment.getName()) == 0) {
			update += processGlobalAssignment(assignment, oldState,valuation);
		} else if (Helper.extractNumber(assignment.getName()) == 1) {
			processLocalAssignment(assignment, oldState, newState, valuation);
		} else {
			System.out
					.println("Error: update to local variable of another module at line "
							+ assignment.getName().getLine());
			System.exit(0);
		}


		
		if (newState.equals(oldState)) {
			if (update.equals("")) {
				update = "true";
			} else {
				update = update.substring(0, update.length() - 1);
			}

		} else {
			if ((!eliminate)
					|| ((variables.abstractValue(oldState) != variables
							.allAssignments().size() - 1) && (variables
							.abstractValue(newState) != variables
							.allAssignments().size() - 1))) {
				update += "(no_" + variables.abstractValue(oldState) + "'=no_"
						+ variables.abstractValue(oldState) + "-1)&(no_"
						+ variables.abstractValue(newState) + "'=no_"
						+ variables.abstractValue(newState) + "+1)";
			} else {
				if (variables.abstractValue(oldState) != variables
						.allAssignments().size() - 1) {
					update += "(no_" + variables.abstractValue(oldState)
							+ "'=no_" + variables.abstractValue(oldState)
							+ "-1)";
				}
				if (variables.abstractValue(newState) != variables
						.allAssignments().size() - 1) {
					update += "(no_" + variables.abstractValue(newState)
							+ "'=no_" + variables.abstractValue(newState)
							+ "+1)";
				}
			}

		}

		return probability + update;
	}

	private void processLocalAssignment(AAtomicAssignment assignment,
			List<Integer> oldState, List<Integer> newState,
			Map<String, Integer> valuation) {
		if (variables.getLocalVariableNames().indexOf(
				Helper.extractName(assignment.getName())) < 0) {
			System.out.println("Error: update unknown local variable at line "
					+ assignment.getName().getLine());
			System.exit(0);
		}

		newState.set(variables.getLocalVariableNames().indexOf(
				Helper.extractName(assignment.getName())), variables.evaluate(
				assignment.getArithmeticExpr(), oldState, valuation, 1));
	}

	private String processGlobalAssignment(AAtomicAssignment assignment,
			List<Integer> oldState, Map<String,Integer> valuation) {
		String result = "";
		if (!variables.globalExists(assignment.getName().getText())) {
			System.out.println("Error: reference to unknown variable at line "
					+ assignment.getName().getLine());
			System.exit(0);
		}
		if (refersOnlyToGlobalsAndLocals(assignment.getArithmeticExpr())) {

			result += "("
					+ assignment.getName().getText()
					+ "'="
					+ partiallyEvaluate(assignment.getArithmeticExpr(),
							oldState,valuation) + ")&";
		} else {
			System.out
					.println("Error: global variable update refers to illegal variables at line "
							+ assignment.getName().getLine());
			System.exit(0);
		}
		return result;
	}

	private boolean refersOnlyToGlobalsAndLocals(PArithmeticExpr arithmeticExpr) {
		return refersOnlyTo(1,variables.getGlobalVariableNames(), arithmeticExpr);
	}

	private String constructSummation(Set<List<Integer>> validStates) {
		List<Integer> abstractValues = new ArrayList<Integer>();
		for (List<Integer> localState : validStates) {
			try {
				abstractValues.add(variables.abstractValue(localState));
			} catch (IllegalLocalAssignmentException e) {
				// Unreachable
			}
		}
		Collections.sort(abstractValues);

		String result = "";
		for (int i = 0; i < abstractValues.size(); i++) {
			result += "no_" + abstractValues.get(i);
			if (i < abstractValues.size() - 1) {
				result += "+";
			}
		}
		return result;
	}

	private String nodeString(Node n) {
		return StringHelper.removeWhitespace(n.toString());
	}
	
	/* PCTL TRANSLATION */

	private String reducedProperty = null;
	
	public void caseAPropertiesSpec(APropertiesSpec node) {
		reducedProperty = "";
		try {
			for(PConstantDeclaration decl : node.getConstantDeclaration()) {
				decl.apply(this);
				reducedProperty += "\n";
			}
			
			for(PPctl prop : node.getPctl()) {
				prop.apply(this);
				reducedProperty += "\n";
			}

			if(eliminate) {
				reducedProperty = reducedProperty.replace("no_" + (variables.allAssignments().size()-1),formulaRHS);
			}

			fw.write(reducedProperty);
			
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void caseTImplies(TImplies node) {
		reducedProperty += " " + node.getText() + " ";
	}

	public void caseALeadingImplication(ALeadingImplication node) {
		reducedProperty += node.toString();
	}
	
	public void caseAProbabilisticPctlBody(AProbabilisticPctlBody node) {
		reducedProperty += node.getProb().getText() + StringHelper.removeWhitespace(node.getBoundop().toString()) +
		StringHelper.removeWhitespace(node.getPctlProbExpr().toString()) + node.getLBracket().getText();
		node.getPathprop().apply(this);
		reducedProperty += node.getRBracket().getText();
	}

	public void caseASteadyStatePctlBody(ASteadyStatePctlBody node) {
		reducedProperty += node.getSteady().getText() + StringHelper.removeWhitespace(node.getBoundop().toString()) +
		StringHelper.removeWhitespace(node.getPctlProbExpr().toString()) + node.getLBracket().getText();
		node.getPctlBody().apply(this);
		reducedProperty += node.getRBracket().getText();
	}
	
	public void caseANextPathprop(ANextPathprop node) {
		reducedProperty += node.getNext().getText() + " ";
		node.getPctlBody().apply(this);
	}

	public void caseAUntilPathprop(AUntilPathprop node) {
		node.getLeft().apply(this);
		reducedProperty += " " + node.getUntil().getText() + " ";
		node.getRight().apply(this);
	}

	public void caseABoundeduntilPathprop(ABoundeduntilPathprop node) {
		node.getLeft().apply(this);
		reducedProperty += " " + node.getUntil().getText() + StringHelper.removeWhitespace(node.getTime().toString()) + " ";
		node.getRight().apply(this);
	}
	
	public void caseASimpleOrExpr(ASimpleOrExpr node) {
		reducedProperty += translateSymmetricGuard(node, false);
	}

	public void caseACompoundOrExpr(ACompoundOrExpr node) {
		reducedProperty += translateSymmetricGuard(node, false);
	}

	public void setLogicOutputFile(String logicOutputFile) throws IOException {
		fw = new FileWriter(logicOutputFile);
	}

	public void caseAConstantDeclaration(AConstantDeclaration node) {
		reducedProperty += node.toString();
	}
	
}
