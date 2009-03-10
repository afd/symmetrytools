package src.translator;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import src.symmetricprism.analysis.DepthFirstAdapter;
import src.symmetricprism.node.AAtomicAssignment;
import src.symmetricprism.node.ACompoundAndExpr;
import src.symmetricprism.node.AGlobalVariable;
import src.symmetricprism.node.AManyAssignment;
import src.symmetricprism.node.AManyStochasticUpdate;
import src.symmetricprism.node.AModule;
import src.symmetricprism.node.AOneAssignment;
import src.symmetricprism.node.AOneStochasticUpdate;
import src.symmetricprism.node.ASimpleOrExpr;
import src.symmetricprism.node.ASpecSpec;
import src.symmetricprism.node.AStatement;
import src.symmetricprism.node.AUpdate;
import src.symmetricprism.node.AVariable;
import src.symmetricprism.node.PArithmeticExpr;
import src.symmetricprism.node.PAssignment;
import src.symmetricprism.node.PGlobalVariable;
import src.symmetricprism.node.PStatement;
import src.symmetricprism.node.PStochasticUpdate;
import src.symmetricprism.node.PVariable;
import src.utilities.StringHelper;

public class Abstractor extends DepthFirstAdapter {

	FileWriter fw;

	VariableSet variables = new VariableSet();
	
	public Abstractor() {
		try {
			fw = new FileWriter("abstract.nm");
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
		
	}

	public void caseASpecSpec(ASpecSpec node) {
		try {
			fw.write(node.getType().toString()+"\n\n");

			for(PGlobalVariable o : node.getGlobalVariable()) {
				variables.addGlobal((AVariable) ((AGlobalVariable) o).getVariable());
			}

			for(int i=0; i<node.getModule().size()-1; i++) {
				for(PVariable o : ((AModule)node.getModule().get(i)).getVariable()) {
					variables.addGlobal((AVariable)o);
				}
			}
			
			node.getModule().get(node.getModule().size()-1).apply(this);
		} catch(IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
	}


	public void caseAModule(AModule node) {
		try {
			fw.write(node.getModuletok()+" " + node.getName() + "\n\n");
			for(PVariable o : node.getVariable()) {
				fw.write(o + "\n");
			}
			fw.write("\n");
			
			for(PStatement o : node.getStatement()) {
				AStatement statement = (AStatement)o;

				List<String> relevantGlobalVariables = variables.globalsUsedToUpdateLocals(statement.getStochasticUpdate());
				
				List<Map<String, Integer>> valuations = variables
				.valuationsOfGlobals(relevantGlobalVariables);

				for(Map<String,Integer> valuation : valuations) {
				
					fw.write("[");
					if(statement.getName()!=null) {
						fw.write(statement.getName().getText());
					}
					fw.write("] ");

					if(statement.getOrExpr() instanceof ASimpleOrExpr &&
							((ASimpleOrExpr)statement.getOrExpr()).getAndExpr() instanceof ACompoundAndExpr) {
						fw.write(((ACompoundAndExpr)((ASimpleOrExpr)statement.getOrExpr()).getAndExpr()).getNotExpr().toString());
					} else {
						fw.write(statement.getOrExpr().toString());
					}

					fw.write(" -> " + abstractStochasticUpdate(statement.getStochasticUpdate(),valuation) + ";\n");
				}
			}
			fw.write("\n");
		
			fw.write(node.getEndmodule().toString()+"\n");
			fw.close();
		} catch(IOException e) {
			e.printStackTrace();
			System.exit(1);
		}
	}

	private String abstractStochasticUpdate(PStochasticUpdate stochasticUpdate, Map<String, Integer> valuation) {
		int noOfOptions = size(stochasticUpdate);

		String result = "";
		
		while(stochasticUpdate instanceof AManyStochasticUpdate) {
			result += "1/" + noOfOptions + ":" + abstractAssignment(((AUpdate)((AManyStochasticUpdate)stochasticUpdate).getUpdate()).getAssignment(),valuation) + "+";
			stochasticUpdate = ((AManyStochasticUpdate)stochasticUpdate).getStochasticUpdate();
		}

		result += "1/" + noOfOptions + ":" + abstractAssignment(((AUpdate)((AOneStochasticUpdate)stochasticUpdate).getUpdate()).getAssignment(),valuation);

		return result;
	
	}

	private String abstractAssignment(PAssignment assignment, Map<String,Integer> valuation) {
		String result = "";

		while(assignment instanceof AManyAssignment) {
			result += abstractAtomicAssignment((AAtomicAssignment)((AManyAssignment)assignment).getAtomicAssignment(),valuation);
			assignment = ((AManyAssignment)assignment).getAssignment();
		}
		result += abstractAtomicAssignment((AAtomicAssignment)((AOneAssignment)assignment).getAtomicAssignment(),valuation);

		if(result == "") {
			return "true";
		}
		// Get rid of trailing &
		return result.substring(0,result.length()-1);
	}

	private String abstractAtomicAssignment(AAtomicAssignment atomicAssignment, Map<String, Integer> valuation) {
		if(Helper.extractNumber(atomicAssignment.getName())==0) {
			return "";
		}

		// The variable is a local
		
		return "(" + atomicAssignment.getName().getText() + atomicAssignment.getAssign().getText() + substituteGlobals(atomicAssignment.getArithmeticExpr(),valuation)+ ")&";
	}

	private String substituteGlobals(PArithmeticExpr arithmeticExpr, Map<String, Integer> valuation) {
		// TODO write this properly, over expression forms
		String result = StringHelper.removeWhitespace(arithmeticExpr.toString());
		
		for(String variable : valuation.keySet()) {
			result = result.replace(variable,String.valueOf(valuation.get(variable)));
		}
		return result;
	}

	private int size(PStochasticUpdate stochasticUpdate) {
		int result = 1;
		for( ; stochasticUpdate instanceof AManyStochasticUpdate; result++) {
			stochasticUpdate = ((AManyStochasticUpdate)stochasticUpdate).getStochasticUpdate();
		}
		return result;
	}
	
}
