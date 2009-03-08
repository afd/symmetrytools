package src.advice;

import java.util.HashSet;
import java.util.Set;

import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AArrayref;
import src.promela.node.AConstFactor;
import src.promela.node.ANumberConst;
import src.promela.node.AParentheseFactor;
import src.promela.node.ARecordVarref;
import src.promela.node.ASimpleAddExpr;
import src.promela.node.ASimpleAndExpr;
import src.promela.node.ASimpleBitandExpr;
import src.promela.node.ASimpleBitorExpr;
import src.promela.node.ASimpleBitxorExpr;
import src.promela.node.ASimpleEqExpr;
import src.promela.node.ASimpleMultExpr;
import src.promela.node.ASimpleOrExpr;
import src.promela.node.ASimpleRelExpr;
import src.promela.node.ASimpleShiftExpr;
import src.promela.node.ASimpleUnExpr;
import src.promela.node.ASingleVarref;
import src.promela.node.PAddExpr;
import src.promela.node.PAndExpr;
import src.promela.node.PBitandExpr;
import src.promela.node.PBitorExpr;
import src.promela.node.PBitxorExpr;
import src.promela.node.PConst;
import src.promela.node.PEqExpr;
import src.promela.node.PFactor;
import src.promela.node.PMultExpr;
import src.promela.node.POrExpr;
import src.promela.node.PRelExpr;
import src.promela.node.PShiftExpr;
import src.promela.node.PUnExpr;
import src.promela.node.PVarref;

public class LocationReferenceCollector extends DepthFirstAdapter {
	
	Set<String> locationReferences;

	public LocationReferenceCollector() {
		locationReferences = new HashSet<String>();
	}
	
	public Set<String> getReferences() {
		return locationReferences;
	}
	
	private Set<String> getReferencedLocations(PVarref varref) {
		
		String locationName = "";

		while(varref instanceof ARecordVarref) {
			
			String newPartOfLocation = ((ARecordVarref)varref).getName().getText();
			
			if (null != ((ARecordVarref)varref).getArrayref()) {
				newPartOfLocation += "[" + compileTimeEvaluateIntegerExpression(((AArrayref)((ARecordVarref)varref).getArrayref()).getOrExpr()) + "]";
				((AArrayref)((ARecordVarref)varref).getArrayref()).getOrExpr().apply(this);		
			}
			
			if(locationName.equals("")) {
				locationName = newPartOfLocation;
			} else {
				locationName = newPartOfLocation + "." + locationName;
			}
			
			varref = ((ARecordVarref)varref).getVarref();
		}
		
		String newPartOfLocation = ((ASingleVarref)varref).getName().getText();
		
		if (null != ((ASingleVarref)varref).getArrayref()) {
			newPartOfLocation += "[" + compileTimeEvaluateIntegerExpression(((AArrayref)((ASingleVarref)varref).getArrayref()).getOrExpr()) + "]";
			((AArrayref)((ASingleVarref)varref).getArrayref()).getOrExpr().apply(this);
		}
		
		if(locationName.equals("")) {
			locationName = newPartOfLocation;
		} else {
			locationName = newPartOfLocation + "." + locationName;
		}
		
		Set<String> result = new HashSet<String>();
		
		result.add(locationName);
		
		return result;
	}

	public void caseASingleVarref(ASingleVarref node) {
		locationReferences.addAll(getReferencedLocations(node));
	}

	public void caseARecordVarref(ARecordVarref node) {
		locationReferences.addAll(getReferencedLocations(node));
	}

	private String compileTimeEvaluateIntegerExpression(POrExpr orExpr) {
		if(orExpr instanceof ASimpleOrExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleOrExpr)orExpr).getAndExpr());
			
		}
		assert(false);
		return null;
	}

	private String compileTimeEvaluateIntegerExpression(PAndExpr andExpr) {
		if(andExpr instanceof ASimpleAndExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleAndExpr)andExpr).getBitorExpr());
		}
		assert(false);
		return null;
	}

	private String compileTimeEvaluateIntegerExpression(PBitorExpr bitorExpr) {
		if(bitorExpr instanceof ASimpleBitorExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleBitorExpr)bitorExpr).getBitxorExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PBitxorExpr bitxorExpr) {
		if(bitxorExpr instanceof ASimpleBitxorExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleBitxorExpr)bitxorExpr).getBitandExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PBitandExpr bitandExpr) {
		if(bitandExpr instanceof ASimpleBitandExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleBitandExpr)bitandExpr).getEqExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PEqExpr eqExpr) {
		if(eqExpr instanceof ASimpleEqExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleEqExpr)eqExpr).getRelExpr());
		}
		assert(false);
		return null;
	}

	private String compileTimeEvaluateIntegerExpression(PRelExpr relExpr) {
		if(relExpr instanceof ASimpleRelExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleRelExpr)relExpr).getShiftExpr());
		}
		assert(false);
		return null;
	}

	private String compileTimeEvaluateIntegerExpression(PShiftExpr shiftExpr) {
		if(shiftExpr instanceof ASimpleShiftExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleShiftExpr)shiftExpr).getAddExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PAddExpr addExpr) {
		if(addExpr instanceof ASimpleAddExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleAddExpr)addExpr).getMultExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PMultExpr multExpr) {
		if(multExpr instanceof ASimpleMultExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleMultExpr)multExpr).getUnExpr());
		}

		// TODO - constant fold!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PUnExpr unExpr) {
		if(unExpr instanceof ASimpleUnExpr) {
			return compileTimeEvaluateIntegerExpression(((ASimpleUnExpr)unExpr).getFactor());
		}

		// TODO - constant fold if it's a bitwise not!
		return "#";
	}

	private String compileTimeEvaluateIntegerExpression(PFactor factor) {
				
		if(factor instanceof AParentheseFactor) {
			return compileTimeEvaluateIntegerExpression(((AParentheseFactor)factor).getOrExpr());
		}

		if(factor instanceof AConstFactor) {
			return compileTimeEvaluateIntegerExpression(((AConstFactor)factor).getConst());
			
		}
		
		return "#";

	}

	private String compileTimeEvaluateIntegerExpression(PConst constant) {
		if(constant instanceof ANumberConst) {
			return ( null == ((ANumberConst)constant).getMinus() ? "" : "-" ) + ((ANumberConst)constant).getNumber().getText();
		}
		
		return "#";

	}
	

}
