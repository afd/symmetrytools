package src.symmextractor;

import junit.framework.Assert;
import src.etch.error.Error;
import src.etch.error.IncomparableTypesException;
import src.etch.typeinference.Unifier;
import src.etch.types.BoolType;
import src.etch.types.ByteType;
import src.etch.types.NumericType;
import src.etch.types.SimpleType;
import src.etch.types.Type;
import src.etch.types.TypeVariableType;
import src.symmextractor.types.PidLiteralCandidate;
import src.symmextractor.types.PidType;

public class PidSensitiveUnifier extends Unifier {

	protected Error unifySubtype(NumericType s, TypeVariableType x) {

		Error result = super.unifySubtype(s, x);
		
		if (s.isSubtype(x.getLower()) && !isPidLiteral(s)) {
			SymmetryChecker.setNotPidLiteral(x.getLower());
		} 
		
		if (s.isSubtype(x.getUpper()) && !isPidLiteral(x.getLower())) {
			SymmetryChecker.setNotPidLiteral(s);
		}
		
		return result;

	}

	protected Error unifySubtype(TypeVariableType x, NumericType s) {

		Error result = super.unifySubtype(x, s);
		
		if (x.getUpper().isSubtype(s) && !isPidLiteral(s)) {
			SymmetryChecker.setNotPidLiteral(x.getUpper());
		}
		
		if (x.getLower().isSubtype(s) && !isPidLiteral(x.getUpper())) {
			SymmetryChecker.setNotPidLiteral(s);
		}
		
		return result;

	}
	
	protected Error checkBounds(TypeVariableType s, Type t) {

		Error result = super.checkBounds(s,t);
		
		if(null == result) {
			if(!(isPidLiteral(s.getUpper()) && isPidLiteral(s.getLower()))) {
				SymmetryChecker.setNotPidLiteral(t);
			}
		}

		return result;
	
	}

	protected Type greatestLowerBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		Type result = super.greatestLowerBound(s,t);

		if(!(isPidLiteral(s.getLower()) && isPidLiteral(t.getLower()))) {
			SymmetryChecker.setNotPidLiteral(result);
		}
		
		return result;
	}

	protected Type leastUpperBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		Type result = super.leastUpperBound(s,t);

		if(!(isPidLiteral(s.getUpper()) && isPidLiteral(t.getUpper()))) {
			SymmetryChecker.setNotPidLiteral(result);
		}

		return result;
	}

	protected void unifyBooleanSubtypes(Type s, Type t) {

		Assert.assertTrue(s.isSubtype(new BoolType()) && t.isSubtype(new BoolType()));
		
		if(!(isPidLiteral(s) && isPidLiteral(t))) {
			SymmetryChecker.setNotPidLiteral(s);
			SymmetryChecker.setNotPidLiteral(t);
		}

	}

	protected void unifyByteTypes(ByteType s, ByteType t) {

		if(!(isPidLiteral(s) && isPidLiteral(t))) {
			SymmetryChecker.setNotPidLiteral(s);
			SymmetryChecker.setNotPidLiteral(t);
		}
	}

	private boolean isPidLiteral(Type t) {
		if(t instanceof PidLiteralCandidate) {
			return ((PidLiteralCandidate)t).isPidLiteral();
		}
		return false;
	}

	protected Error unifyConstraintOnSimpleTypes(SimpleType s, SimpleType t) {

		Error result = super.unifyConstraintOnSimpleTypes(s, t);
		
		if(null != result) {
		
			if(s instanceof PidType && t instanceof PidType) {
				return null;
			}
			
			if(s instanceof PidType && isPidLiteral(t)) {
				rep.put(t,s);
				return null;
			}
	
			if(t instanceof PidType && isPidLiteral(s)) {
				rep.put(s,t);
				return null;
			}
			
		}

		return result;
	
	}
		
}
