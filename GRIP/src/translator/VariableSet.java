package src.translator;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import src.exceptions.BadlyInitialisedVariableException;
import src.exceptions.IllegalLocalAssignmentException;
import src.symmetricprism.node.AAtomicAssignment;
import src.symmetricprism.node.AAtomicFactor;
import src.symmetricprism.node.ACommaArithmeticExpr;
import src.symmetricprism.node.ACompoundAndExpr;
import src.symmetricprism.node.ACompoundNotExpr;
import src.symmetricprism.node.ACompoundOrExpr;
import src.symmetricprism.node.ADivMultDivExpr;
import src.symmetricprism.node.AEqualsAtomicFactor;
import src.symmetricprism.node.AEqualsRangeAtomicFactor;
import src.symmetricprism.node.AGtAtomicFactor;
import src.symmetricprism.node.AGteAtomicFactor;
import src.symmetricprism.node.AInitialisation;
import src.symmetricprism.node.ALtAtomicFactor;
import src.symmetricprism.node.ALteAtomicFactor;
import src.symmetricprism.node.AManyAssignment;
import src.symmetricprism.node.AManyStochasticUpdate;
import src.symmetricprism.node.AMaxArithmeticFactor;
import src.symmetricprism.node.AMinArithmeticFactor;
import src.symmetricprism.node.AMinusArithmeticExpr;
import src.symmetricprism.node.AMultMultDivExpr;
import src.symmetricprism.node.ANameArithmeticFactor;
import src.symmetricprism.node.ANequalsAtomicFactor;
import src.symmetricprism.node.ANequalsRangeAtomicFactor;
import src.symmetricprism.node.ANumberArithmeticFactor;
import src.symmetricprism.node.AOneAssignment;
import src.symmetricprism.node.AOneStochasticUpdate;
import src.symmetricprism.node.AParentheseArithmeticFactor;
import src.symmetricprism.node.AParenthesisFactor;
import src.symmetricprism.node.APlusArithmeticExpr;
import src.symmetricprism.node.ARange;
import src.symmetricprism.node.ASimpleAndExpr;
import src.symmetricprism.node.ASimpleArithmeticExpr;
import src.symmetricprism.node.ASimpleMultDivExpr;
import src.symmetricprism.node.ASimpleNotExpr;
import src.symmetricprism.node.ASimpleOrExpr;
import src.symmetricprism.node.AUpdate;
import src.symmetricprism.node.AVariable;
import src.symmetricprism.node.PAndExpr;
import src.symmetricprism.node.PArithmeticExpr;
import src.symmetricprism.node.PArithmeticFactor;
import src.symmetricprism.node.PAssignment;
import src.symmetricprism.node.PAtomicAssignment;
import src.symmetricprism.node.PAtomicFactor;
import src.symmetricprism.node.PCommaArithmeticExpr;
import src.symmetricprism.node.PFactor;
import src.symmetricprism.node.PMultDivExpr;
import src.symmetricprism.node.PNotExpr;
import src.symmetricprism.node.POrExpr;
import src.symmetricprism.node.PStochasticUpdate;
import src.symmetricprism.node.PUpdate;

public class VariableSet {

	private List<String> localVariableNames;
	private List<VarEntry> localVariableEntries;

	private List<String> globalVariableNames;
	private List<VarEntry> globalVariableEntries;

	private boolean performReachabilityAnalysis;
	private List<List<Integer>> localStates;

	public VariableSet() {
		this(false);
	}
	
	public VariableSet(boolean optimisationOn) {
		localVariableNames = new ArrayList<String>();
		localVariableEntries = new ArrayList<VarEntry>();
		globalVariableNames = new ArrayList<String>();
		globalVariableEntries = new ArrayList<VarEntry>();
		performReachabilityAnalysis = optimisationOn;
	}
	
	public boolean putLocal(String name, VarEntry var) {
		if(localNameExists(name)) {
			return false;
		}
		localVariableNames.add(name);
		localVariableEntries.add(var);
		return true;
	}

	private boolean putGlobal(String name, VarEntry var) {
		if(globalNameExists(name)) {
			return false;
		}
		globalVariableNames.add(name);
		globalVariableEntries.add(var);
		return true;
	}
	
	public int abstractValue(List<Integer> assignment) throws IllegalLocalAssignmentException {
		int result = 0;
		for(List<Integer> x : allAssignments()) {
			if(x.equals(assignment)) {
				return result;
			}
			result++;
		}
		
		throw new IllegalLocalAssignmentException(assignment);
		
	}
	
	private boolean localNameExists(String name) {
		return localVariableNames.contains(name);
	}

	private boolean globalNameExists(String name) {
		return globalVariableNames.contains(name);
	}

	List<Map<String,Integer>> valuationsOfGlobals(List<String> globalNames) {
		List<Map<String,Integer>> result = new ArrayList<Map<String,Integer>>();
		
		List<Integer> valuation = new ArrayList<Integer>();
		
		for(String varName : globalNames) {
			valuation.add(globalVariableEntries.get(globalVariableNames.indexOf(varName)).getLower());
		}

		for(;;) {
			Map<String,Integer> valuationMap = new HashMap<String,Integer>();
			for(int i=0; i<globalNames.size(); i++) {
				valuationMap.put(globalNames.get(i),valuation.get(i));
			}
			result.add(valuationMap);
			if(!incrementGlobalValuation(valuation,globalNames)) {
				break;
			}
		}
		
		
		return result;
	}
	
	private boolean incrementGlobalValuation(List<Integer> valuation, List<String> globalNames) {

		for(int i=globalNames.size()-1; i>=0; i--) {
			if(valuation.get(i)<globalVariableEntries.get(globalVariableNames.indexOf(globalNames.get(i))).getUpper()) {
				valuation.set(i,valuation.get(i)+1);
				return true;
			}
			
			if(i==0) {
				return false;
			}
			
			valuation.set(i,globalVariableEntries.get(globalVariableNames.indexOf(globalNames.get(i))).getLower());

		}
		
		// unreachable
		return false;

	}

	private static boolean isOSWindows() {
		return System.getProperty("os.name").length()>="Windows".length() && System.getProperty("os.name").substring(0,7).equals("Windows");
	}
	
	public List<List<Integer>> allAssignments() {
		if(localStates == null) {

			List<List<Integer>> allLocalStates = allPossibleLocalStates();
			if(!performReachabilityAnalysis) {
				localStates = allLocalStates;
			} else {
				
				localStates = new ArrayList<List<Integer>>();
				outputPCTLProperties(allLocalStates);

				Process p;
				try {
					if(isOSWindows()) {
						p = Runtime.getRuntime().exec("prism.bat -noprobchecks -fixdl abstract.nm localstates.pctl");
					} else {
						p = Runtime.getRuntime().exec("prism -noprobchecks -fixdl abstract.nm localstates.pctl");
					}

					BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()));

					int noStatesChecked = 0;
					while(noStatesChecked<allLocalStates.size()) {
						
						String line = br.readLine();
					
						if(line.contains("Result: true")) {
							noStatesChecked++;
						} else if(line.contains("Result: false")) {
							localStates.add(allLocalStates.get(noStatesChecked));
							noStatesChecked++;
						}
					}
					
					p.waitFor();
				} catch (IOException e) {
					System.out.println("Error executing PRISM using -optimise optimisation.  Make sure \"prism\" (Unix) or \"prism.bat\" (Windows) are in your path.");
					System.exit(1);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}

		}

		return localStates;
	}

	private void outputPCTLProperties(List<List<Integer>> allLocalStates) {
		try {
			FileWriter fw = new FileWriter("localstates.pctl");
			for(List<Integer> localState : allLocalStates) {
				fw.write("!(");
				for(int i=0; i<localState.size(); i++) {
					fw.write("("+localVariableNames.get(i)+"1="+localState.get(i)+")");
					if(i<localState.size()-1) {
						fw.write("&");
					}
				}
				fw.write(")\n");
			}
			fw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private List<List<Integer>> allPossibleLocalStates() {
		List<List<Integer>> result = new ArrayList<List<Integer>>();

		List<Integer> current = new ArrayList<Integer>();
		for(VarEntry var : localVariableEntries) {
			current.add(var.getLower());
		}

		for(;;) {

			result.add(new ArrayList<Integer>(current));
			if(!incrementLocalValuation(current)) {
				break;
			}
		}

		return result;		
	}
	
	private boolean incrementLocalValuation(List<Integer> current) {
		for(int i=localVariableEntries.size()-1; i>=0; i--) {
			if(current.get(i)<localVariableEntries.get(i).getUpper()) {
				current.set(i,current.get(i)+1);
				return true;
			}
			
			if(i==0) {
				return false;
			}
			
			current.set(i,localVariableEntries.get(i).getLower());

		}
		
		// unreachable
		return false;
	}

	public boolean satisfies(PAtomicFactor atomicFactor, List<Integer> assignment, int moduleNo) {
		Map<String,Integer> nullValuation = new HashMap<String,Integer>();
		if(atomicFactor instanceof AEqualsRangeAtomicFactor) {
			return Helper.extractRange((ARange) ((AEqualsRangeAtomicFactor)atomicFactor).getRange()).contains(evaluate(((AEqualsRangeAtomicFactor)atomicFactor).getArithmeticExpr(),assignment,nullValuation,moduleNo));
		} else if(atomicFactor instanceof ANequalsRangeAtomicFactor) {
			return !Helper.extractRange((ARange) ((ANequalsRangeAtomicFactor)atomicFactor).getRange()).contains(evaluate(((ANequalsRangeAtomicFactor)atomicFactor).getArithmeticExpr(),assignment,nullValuation,moduleNo));
		} else if(atomicFactor instanceof AEqualsAtomicFactor) {
			return evaluate(((AEqualsAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)==evaluate(((AEqualsAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);
		} else if(atomicFactor instanceof ANequalsAtomicFactor) {
			return evaluate(((ANequalsAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)!=evaluate(((ANequalsAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);
		} else if(atomicFactor instanceof AGtAtomicFactor) {
			return evaluate(((AGtAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)>evaluate(((AGtAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);
		} else if(atomicFactor instanceof AGteAtomicFactor) {
			return evaluate(((AGteAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)>=evaluate(((AGteAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);
		} else if(atomicFactor instanceof ALtAtomicFactor) {
			return evaluate(((ALtAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)<evaluate(((ALtAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);
		}
		return evaluate(((ALteAtomicFactor)atomicFactor).getLeft(),assignment,nullValuation,moduleNo)<=evaluate(((ALteAtomicFactor)atomicFactor).getRight(),assignment,nullValuation,moduleNo);

	}

	int evaluate(PArithmeticExpr expr, List<Integer> assignment, Map<String, Integer> valuation, int moduleNo) {
		if(expr instanceof ASimpleArithmeticExpr) {
			return evaluate(((ASimpleArithmeticExpr)expr).getMultDivExpr(),assignment,valuation,moduleNo);
		} else if(expr instanceof APlusArithmeticExpr) {
			return evaluate(((APlusArithmeticExpr)expr).getArithmeticExpr(),assignment,valuation,moduleNo) + evaluate(((APlusArithmeticExpr)expr).getMultDivExpr(),assignment,valuation,moduleNo);
		}
		return evaluate(((AMinusArithmeticExpr)expr).getArithmeticExpr(),assignment,valuation,moduleNo) - evaluate(((AMinusArithmeticExpr)expr).getMultDivExpr(),assignment,valuation,moduleNo);
	}

	int evaluate(PMultDivExpr expr, List<Integer> assignment, Map<String, Integer> valuation, int moduleNo) {
		if(expr instanceof ASimpleMultDivExpr) {
			return evaluate(((ASimpleMultDivExpr)expr).getArithmeticFactor(),assignment,valuation,moduleNo);
		} else if(expr instanceof AMultMultDivExpr) {
			return evaluate(((AMultMultDivExpr)expr).getMultDivExpr(),assignment,valuation,moduleNo) * evaluate(((AMultMultDivExpr)expr).getArithmeticFactor(),assignment,valuation,moduleNo);
		}
		return evaluate(((ADivMultDivExpr)expr).getMultDivExpr(),assignment,valuation,moduleNo) / evaluate(((ADivMultDivExpr)expr).getArithmeticFactor(),assignment,valuation,moduleNo);
	}

	int evaluate(PArithmeticFactor factor, List<Integer> assignment, Map<String, Integer> valuation, int moduleNo) {
		if(factor instanceof ANumberArithmeticFactor) {
			return Helper.toInt(((ANumberArithmeticFactor)factor).getNumber().getText());
		} else if(factor instanceof ANameArithmeticFactor) {
			String name = Helper.extractName(((ANameArithmeticFactor)factor).getName());
			int number = Helper.extractNumber(((ANameArithmeticFactor)factor).getName());
			if(number==0) {
				return valuation.get(name);
			}
			if(!localVariableNames.contains(name) || number!=moduleNo) {
				System.out.println("Inappropriate variable used in local expression at line " + ((ANameArithmeticFactor)factor).getName().getLine() +".");
			}
			return assignment.get(localVariableNames.indexOf(name));
		} else if(factor instanceof AMinArithmeticFactor) {
			int min = evaluate(((AMinArithmeticFactor)factor).getArithmeticExpr(),assignment,valuation,moduleNo);
			for(Object o : ((AMinArithmeticFactor)factor).getCommaArithmeticExpr()) {
				min = Math.min(min, evaluate(((ACommaArithmeticExpr)o).getArithmeticExpr(),assignment,valuation,moduleNo));
			}
			return min;
		} else if(factor instanceof AMaxArithmeticFactor) {
			int max = evaluate(((AMaxArithmeticFactor)factor).getArithmeticExpr(),assignment,valuation,moduleNo);
			for(Object o : ((AMaxArithmeticFactor)factor).getCommaArithmeticExpr()) {
				max = Math.max(max, evaluate(((ACommaArithmeticExpr)o).getArithmeticExpr(),assignment,valuation,moduleNo));
			}
			return max;
		}
		return evaluate(((AParentheseArithmeticFactor)factor).getArithmeticExpr(),assignment,valuation,moduleNo);
	}

	public Set<List<Integer>> satisfies(PAtomicFactor atomicFactor, int moduleNo) {
		Set<List<Integer>> result = new HashSet<List<Integer>>();
		for(List<Integer> assignment : allAssignments()) {
			if(satisfies(atomicFactor,assignment,moduleNo)) {
				result.add(assignment);
			}
		}
		return result;
	}

	public List<VarEntry> getVariableEntries() {
		return Collections.unmodifiableList(localVariableEntries);
	}

	public List<String> getLocalVariableNames() {
		return Collections.unmodifiableList(localVariableNames);
	}

	public List<Integer> getInitialAssignment() {
		List<Integer> result = new ArrayList<Integer>();
		for(VarEntry varEntry : localVariableEntries) {
			result.add(varEntry.getInit());
		}
		return result;
	}

	protected Set<List<Integer>> satisfies(POrExpr orExpr, int moduleNo) {
		if(orExpr instanceof ASimpleOrExpr) {
			return satisfies(((ASimpleOrExpr)orExpr).getAndExpr(), moduleNo);
		}
		
		Set<List<Integer>> result = new HashSet<List<Integer>>();
		
		result.addAll(satisfies(((ACompoundOrExpr)orExpr).getAndExpr(),moduleNo));
		result.addAll(satisfies(((ACompoundOrExpr)orExpr).getOrExpr(),moduleNo));

		return result;
	}

	protected Set<List<Integer>> satisfies(PAndExpr andExpr, int moduleNo) {
		if(andExpr instanceof ASimpleAndExpr) {
			return satisfies(((ASimpleAndExpr)andExpr).getNotExpr(), moduleNo);
		}
		
		Set<List<Integer>> result = new HashSet<List<Integer>>();
		
		result.addAll(satisfies(((ACompoundAndExpr)andExpr).getNotExpr(),moduleNo));
		result.retainAll(satisfies(((ACompoundAndExpr)andExpr).getAndExpr(),moduleNo));

		return result;
	}

	protected Set<List<Integer>> satisfies(PNotExpr notExpr, int moduleNo) {
		if(notExpr instanceof ASimpleNotExpr) {
			return satisfies(((ASimpleNotExpr)notExpr).getFactor(),moduleNo);
		}

		Set<List<Integer>> result = new HashSet<List<Integer>>();
		result.addAll(allAssignments());
		result.removeAll(satisfies(((ACompoundNotExpr)notExpr).getFactor(),moduleNo));

		return result;
	}

	private Set<List<Integer>> satisfies(PFactor factor, int moduleNo) {
		if(factor instanceof AParenthesisFactor) {
			return satisfies(((AParenthesisFactor)factor).getOrExpr(),moduleNo);
		}
		return satisfies(((AAtomicFactor)factor).getAtomicFactor(),moduleNo);
	}

	public boolean globalExists(String name) {
		return globalVariableNames.contains(name);
	}

	public Set<String> getGlobalVariableNames() {
		return new HashSet<String>(globalVariableNames);
	}

	public void addGlobal(AVariable var) {
		try {
			String name = Helper.extractName(var.getName());
			int moduleNumber = Helper.extractNumber(var.getName());
			int lower = Helper.toInt(var.getLow().getText());
			int upper = Helper.toInt(var.getHigh().getText());
			int start = (var.getInitialisation() != null ? Helper
					.toInt(((AInitialisation) var.getInitialisation())
							.getNumber().getText()) : lower);

			if (moduleNumber != 0) {
				System.out
						.println("Error at line "
								+ var.getName().getLine()
								+ " - global variable names must not contain numeric characters");
				System.exit(0);
			}

			if (!putGlobal(name,
					new VarEntry(lower, upper, start))) {
				System.out.println("Error at line "
						+ var.getName().getLine() + ": variable name "
						+ name + " already used");
				System.exit(0);
			}

		} catch (BadlyInitialisedVariableException e) {
			System.out.println(e);
			System.exit(0);
		}
	}

	
	public List<String> globalsUsedToUpdateLocals(
			PStochasticUpdate stochasticUpdate) {
		Set<String> globalNames = new HashSet<String>();

		while (stochasticUpdate instanceof AManyStochasticUpdate) {
			globalNames
					.addAll(globalsUsedToUpdateLocals(((AManyStochasticUpdate) stochasticUpdate)
							.getUpdate()));
			stochasticUpdate = ((AManyStochasticUpdate) stochasticUpdate)
					.getStochasticUpdate();
		}
		globalNames
				.addAll(globalsUsedToUpdateLocals(((AOneStochasticUpdate) stochasticUpdate)
						.getUpdate()));

		List<String> result = new ArrayList<String>();
		result.addAll(globalNames);
		return result;
	}

	private Set<String> globalsUsedToUpdateLocals(PUpdate update) {
		Set<String> result = new HashSet<String>();

		PAssignment assignment = ((AUpdate) update).getAssignment();

		while (assignment instanceof AManyAssignment) {
			result
					.addAll(globalsUsedToUpdateLocals(((AManyAssignment) assignment)
							.getAtomicAssignment()));
			assignment = ((AManyAssignment) assignment).getAssignment();
		}
		result.addAll(globalsUsedToUpdateLocals(((AOneAssignment) assignment)
				.getAtomicAssignment()));

		return result;
	}

	private Set<String> globalsUsedToUpdateLocals(
			PAtomicAssignment atomicAssignment) {
		if (Helper.extractNumber(((AAtomicAssignment) atomicAssignment)
				.getName()) == 1) {
			return globalVariableNamesReferredToBy(((AAtomicAssignment) atomicAssignment)
					.getArithmeticExpr());
		}
		return new HashSet<String>();
	}

	private Set<String> globalVariableNamesReferredToBy(
			PArithmeticExpr arithmeticExpr) {
		if (arithmeticExpr instanceof ASimpleArithmeticExpr) {
			return globalVariableNamesReferredToBy(((ASimpleArithmeticExpr) arithmeticExpr)
					.getMultDivExpr());
		}
		Set<String> result = new HashSet<String>();
		if (arithmeticExpr instanceof APlusArithmeticExpr) {
			result
					.addAll(globalVariableNamesReferredToBy(((APlusArithmeticExpr) arithmeticExpr)
							.getArithmeticExpr()));
			result
					.addAll(globalVariableNamesReferredToBy(((APlusArithmeticExpr) arithmeticExpr)
							.getMultDivExpr()));
			return result;
		}
		result
				.addAll(globalVariableNamesReferredToBy(((AMinusArithmeticExpr) arithmeticExpr)
						.getArithmeticExpr()));
		result
				.addAll(globalVariableNamesReferredToBy(((AMinusArithmeticExpr) arithmeticExpr)
						.getMultDivExpr()));
		return result;
	}

	private Set<String> globalVariableNamesReferredToBy(PMultDivExpr multDivExpr) {
		if (multDivExpr instanceof ASimpleMultDivExpr) {
			return globalVariableNamesReferredToBy(((ASimpleMultDivExpr) multDivExpr)
					.getArithmeticFactor());
		}
		Set<String> result = new HashSet<String>();
		if (multDivExpr instanceof AMultMultDivExpr) {
			result
					.addAll(globalVariableNamesReferredToBy(((AMultMultDivExpr) multDivExpr)
							.getMultDivExpr()));
			result
					.addAll(globalVariableNamesReferredToBy(((AMultMultDivExpr) multDivExpr)
							.getArithmeticFactor()));
			return result;
		}
		result
				.addAll(globalVariableNamesReferredToBy(((ADivMultDivExpr) multDivExpr)
						.getMultDivExpr()));
		result
				.addAll(globalVariableNamesReferredToBy(((ADivMultDivExpr) multDivExpr)
						.getArithmeticFactor()));
		return result;
	}

	private Set<String> globalVariableNamesReferredToBy(
			PArithmeticFactor arithmeticFactor) {
		if (arithmeticFactor instanceof ANumberArithmeticFactor) {
			return new HashSet<String>();
		}

		if (arithmeticFactor instanceof AParentheseArithmeticFactor) {
			return globalVariableNamesReferredToBy(((AParentheseArithmeticFactor) arithmeticFactor)
					.getArithmeticExpr());
		}

		Set<String> result = new HashSet<String>();

		if (arithmeticFactor instanceof ANameArithmeticFactor) {
			if (Helper.extractNumber(((ANameArithmeticFactor) arithmeticFactor)
					.getName()) == 0) {
				result.add(Helper
						.extractName(((ANameArithmeticFactor) arithmeticFactor)
								.getName()));
			}
			return result;
		}

		PArithmeticExpr first;
		List<PCommaArithmeticExpr> others;

		if (arithmeticFactor instanceof AMinArithmeticFactor) {
			first = ((AMinArithmeticFactor) arithmeticFactor)
					.getArithmeticExpr();
			others = ((AMinArithmeticFactor) arithmeticFactor)
					.getCommaArithmeticExpr();
		} else {
			first = ((AMaxArithmeticFactor) arithmeticFactor)
					.getArithmeticExpr();
			others = ((AMaxArithmeticFactor) arithmeticFactor)
					.getCommaArithmeticExpr();
		}

		result.addAll(globalVariableNamesReferredToBy(first));
		for (Object o : others) {
			result
					.addAll(globalVariableNamesReferredToBy(((ACommaArithmeticExpr) o)
							.getArithmeticExpr()));
		}
		return result;
	}

	public VarEntry getGlobalEntry(String name) {
		return globalVariableEntries.get(globalVariableNames.indexOf(name));
	}

	public VarEntry getLocalEntry(String name) {
		return localVariableEntries.get(localVariableNames.indexOf(name));
	}

	
}
