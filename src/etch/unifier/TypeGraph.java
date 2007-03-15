package src.etch.unifier;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

import src.etch.error.Error;
import src.etch.error.IncompatibleTypesError;
import src.etch.error.MismatchedArgumentsError;
import src.etch.error.SubtypingError;
import src.etch.types.ArrayType;
import src.etch.types.BoolType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.IncomparableTypesException;
import src.etch.types.IntType;
import src.etch.types.Minimiser;
import src.etch.types.MtypeType;
import src.etch.types.NumericType;
import src.etch.types.PidType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.ShortType;
import src.etch.types.Type;
import src.etch.types.TypeSubstituter;
import src.etch.types.TypeVariableType;

public class TypeGraph {

	private Map<Type,Type> rep;

	protected TypeGraph() {
		rep = new HashMap<Type,Type>();
	}
			
	protected Error unifyConstraint(SubtypingConstraint sc, List<EqualityConstraint> equalityConstraints) {

		if(!rep.containsKey(sc.getLhs())) {
			rep.put(sc.getLhs(),sc.getLhs());
		}
		if(!rep.containsKey(sc.getRhs())) {
			rep.put(sc.getRhs(),sc.getRhs());
		}
		
		Type s = rep(sc.getLhs());
		Type t = rep(sc.getRhs());
		
		if (s instanceof TypeVariableType && t instanceof NumericType) {
			return unifySubtype((TypeVariableType) s, (NumericType) t);
		} else if (t instanceof TypeVariableType && s instanceof NumericType) {
			return unifySubtype((NumericType)s, (TypeVariableType) t);
		} else {
			equalityConstraints.add(new EqualityConstraint(s,t,sc.getLine()));
			return null;
		}
	}

	private Error unifySubtype(NumericType s, TypeVariableType x) {

		/* We have s<:x, where s is a numeric type */
		
		if (x.getLower() == null) {
			x.setLower(s);
			return null;
		} else if (s.isSubtype(x.getLower())) {
			if(!s.isPidLiteral()) {
				x.getLower().setNotPidLiteral();
			}
			return null;
		} else if (x.getLower().isSubtype(s)) {
			if ((x.getUpper() == null)
					|| (s.isSubtype(x.getUpper()))) {
				if(!x.getLower().isPidLiteral()) {
					s.setNotPidLiteral();
				}
				x.setLower(s);
				return null;
			}
			return new SubtypingError(s.name(),x.getUpper().name());
		} else {
			Assert.assertTrue(false);
			return null;
		}
	}

	private Error unifySubtype(TypeVariableType x, NumericType s) {
		if (x.getUpper() == null) {
			x.setUpper(s);
			return null;
		} else if (x.getUpper().isSubtype(s)) {
			if(!s.isPidLiteral()) {
				x.getUpper().setNotPidLiteral();
			}
			return null;
		} else if (s.isSubtype(x.getUpper())) {
			if ((x.getLower() == null)
					|| (x.getLower().isSubtype(s))) {
				if(!x.getUpper().isPidLiteral()) {
					s.setNotPidLiteral();
				}
				x.setUpper(s);
				return null;
			}
			return new SubtypingError(applySubstitutionsAndMinimise(x.getLower()).name(),
					s.name());
		} else {
			Assert.assertTrue(false);
			return null;
		}
	}
	
	protected Error unifyConstraint(Type left, Type right) {

		if(!rep.containsKey(left)) {
			rep.put(left,left);
		}

		if(!rep.containsKey(right)) {
			rep.put(right,right);
		}
		
		Type s = rep(left);
		Type t = rep(right);

		if (s instanceof TypeVariableType || t instanceof TypeVariableType) {
			return union(s, t);
		}

		if(s instanceof MtypeType && t instanceof MtypeType) {
			return null;
		}

		if(s.isSubtype(new BoolType()) && t.isSubtype(new BoolType())) {
			if((s instanceof NumericType && !((NumericType)s).isPidLiteral())||(t instanceof NumericType && !((NumericType)t).isPidLiteral())) {
				s.setNotPidLiteral();
				t.setNotPidLiteral();
			}
			return null;
		}
		
		if(s instanceof RecordType && t instanceof RecordType && s.equal(t)) {
			return null;
		}

		if(s instanceof ByteType && t instanceof ByteType) {
			if(!(((ByteType)s).isPidLiteral()&&((ByteType)t).isPidLiteral())) {
				s.setNotPidLiteral();
				t.setNotPidLiteral();
			}
			return null;
		}
		
		if(s instanceof ShortType && t instanceof ShortType) {
			return null;
		}
		
		if(s instanceof IntType && t instanceof IntType) {
			return null;
		}

		if(s instanceof PidType && t instanceof PidType) {
			return null;
		}
		
		if(s instanceof PidType && (t instanceof NumericType && ((NumericType)t).isPidLiteral())) {
			rep.put(t,s);
			return null;
		}

		if(t instanceof PidType && (s instanceof NumericType && ((NumericType)s).isPidLiteral())) {
			rep.put(s,t);
			return null;
		}

		if (s instanceof ChanType && t instanceof ChanType) {
			union(s, t);
			return (unifyConstraint(((ChanType)s).getMessageType(), ((ChanType)t).getMessageType()));
		}

		if (s instanceof ArrayType && t instanceof ArrayType) {
			union(s, t);
			if(((ArrayType)s).getLength()!=((ArrayType)t).getLength()) {
				return new IncompatibleTypesError(applySubstitutionsAndMinimise(s).name(),applySubstitutionsAndMinimise(t).name());
			}
			Error result = unifyConstraint(((ArrayType)s).getElementType(),
					((ArrayType)t).getElementType());
			if (result == null) {
				result = unifyConstraint(((ArrayType)s).getIndexType(), ((ArrayType)t).getIndexType());
			}
			return result;
		}

		if (s instanceof ProductType && t instanceof ProductType) {
			if (((ProductType) s).getArity()==((ProductType) t).getArity()) {
				union(s, t);
				Error result = null;
				for(int i=0; i < ((ProductType) s).getArity() && (result == null); i++) {
					result = unifyConstraint(((ProductType) s).getTypeOfPosition(i), ((ProductType) t)
							.getTypeOfPosition(i));
				}
				return result;
			}
			return new MismatchedArgumentsError(((ProductType) s).getArity(), ((ProductType) t).getArity());
		}
		
		return new IncompatibleTypesError(applySubstitutionsAndMinimise(s).name(), applySubstitutionsAndMinimise(t).name());
	}

	public Type rep(Type t) {
		if(!rep.containsKey(t)) {
			// This should only be called during substitution, with a type
			// that was never added to the the type graph during unification.
			return t;
		} else {
			Assert.assertNotNull(rep.get(t));
			Type previous = t;
			Type current = (Type)rep.get(t);
			while(current != previous) {
				previous = current;
				current = (Type)rep.get(previous);
			}
			return current;
		}
	}

	private Error union(Type s, Type t) {
		// s and t are assumed to be equivalence class representatives

		Error result = null;
		
		if (s instanceof TypeVariableType && t instanceof TypeVariableType) {
			result = recomputeBounds((TypeVariableType)s, (TypeVariableType) t);
			rep.put(t,s);
		} 
		
		else if (s instanceof TypeVariableType) {
			result = checkBounds((TypeVariableType) s, t);
			rep.put(s,t);
		} 
		
		else if (t instanceof TypeVariableType) {
			result = checkBounds((TypeVariableType) t,s);
			rep.put(t,s);
		} 
		
		else {
			rep.put(t,s);
		}
		
		return result;
	}

	private Error recomputeBounds(TypeVariableType s, TypeVariableType t) {
		// If they are both type variables then we need to check that
		// upper(s) and upper(t) are comparable,
		// lower(s) and lower(t) are comparable,
		// max(lower(s),lower(t)) <: min(upper(s),upper(t))
		// change bounds of s to be these new bounds
		// t.setRep(s);
		try {
			NumericType newUpper = leastUpperBound(s,t);
			NumericType newLower = greatestLowerBound(s,t);

			if ((newLower != null) && (newUpper != null)
					&& !(newLower.isSubtype(newUpper))) {
				return new SubtypingError(applySubstitutionsAndMinimise(newLower)
						.name(), applySubstitutionsAndMinimise(newUpper).name());
			}

			s.setLower(newLower);
			s.setUpper(newUpper);
			return null;

		} catch (IncomparableTypesException e) {
			return new IncompatibleTypesError(applySubstitutionsAndMinimise(e.getLeftType()).name(), applySubstitutionsAndMinimise(e.getRightType()).name());
		}
	}

	private Error checkBounds(TypeVariableType s, Type t) {
		if(s.getLower()==null && s.getUpper()==null) {
			return null;
		}
		
		if ((s.getLower() != null) && !(s.getLower().isSubtype(t) || (s.getLower().isPidLiteral() && t instanceof PidType))) {
			return new SubtypingError(s.getLower().name(), applySubstitutionsAndMinimise(t).name());
		} else if ((s.getUpper() != null) && !(t.isSubtype(s.getUpper()) || (s.getUpper().isPidLiteral() && t instanceof PidType))) {
			return new SubtypingError(applySubstitutionsAndMinimise(t).name(), s.getUpper().name());
		} else {
			if(!((s.getUpper()==null || s.getUpper().isPidLiteral()) && (s.getLower()==null || s.getLower().isPidLiteral()))) {
				t.setNotPidLiteral();
			}
			return null;
		}
	}

	private Type applySubstitutionsAndMinimise(Type t) {
		return Minimiser.minimise(new TypeSubstituter(this).applySubstitutions(t));
	}

	private NumericType greatestLowerBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		if ((s.getLower() != null) && (t.getLower() != null)) {
			NumericType result = (NumericType)Type.max(s.getLower(), t.getLower());
			if(!(s.getLower().isPidLiteral() && t.getLower().isPidLiteral())) {
				result.setNotPidLiteral();
			}
			return result;
		} else if (s.getLower() != null) {
			return s.getLower();
		} else if (t.getLower() != null) {
			return t.getLower();
		}
		return null;
	}

	private NumericType leastUpperBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		if ((s.getUpper() != null) && (t.getUpper() != null)) {
			NumericType result = (NumericType)Type.min(s.getUpper(), t.getUpper());
			if(!(s.getUpper().isPidLiteral() && t.getUpper().isPidLiteral())) {
				result.setNotPidLiteral();
			}
			return result;
		} else if (s.getUpper() != null) {
			return s.getUpper();
		} else if (t.getUpper() != null) {
			return t.getUpper();
		}
		return null;
	}
	
	public String toString() {
		String result = "";
		Iterator i = rep.keySet().iterator();
		while (i.hasNext()) {
			Type tv = (Type) i.next();
			if(tv instanceof TypeVariableType) {
				result = result + tv.name() + " |-> " + applySubstitutionsAndMinimise(tv) + ";\n";
			}
		}
		return result;
	}

	public String showRep() {
		String result = "";
		Iterator i = rep.keySet().iterator();
		while (i.hasNext()) {
			Type tv = (Type) i.next();
			result = result + tv.name() + " |-> " + ((Type) rep.get(tv)).name() + ";\n";
		}
		return result;		
	}

}