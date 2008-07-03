package src.etch.typeinference;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;
import src.etch.error.Error;
import src.etch.error.IncomparableTypesException;
import src.etch.error.IncompatibleTypesError;
import src.etch.error.MismatchedArgumentsError;
import src.etch.error.SubtypingError;
import src.etch.types.AnyType;
import src.etch.types.ArrayType;
import src.etch.types.BoolType;
import src.etch.types.BottomType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.IntType;
import src.etch.types.Minimiser;
import src.etch.types.MtypeType;
import src.etch.types.NumericType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.ShortType;
import src.etch.types.SimpleType;
import src.etch.types.Type;
import src.etch.types.TypeVariableType;

public class Unifier {

	protected Map<Type,Type> rep;
	
	public Unifier() {
		rep = new HashMap<Type,Type>();
	}
			
	protected Error unifySubtypingConstraint(SubtypingConstraint sc, List<EqualityConstraint> equalityConstraints) {

		Assert.assertFalse(sc.getLhs() instanceof TypeVariableType && sc.getRhs() instanceof TypeVariableType);

		if(sc.getLhs() instanceof BottomType) {
			return null;
		}
		
		if((sc.getLhs() instanceof SimpleType) && (sc.getRhs() instanceof SimpleType))
		{
			if(!(sc.getLhs() instanceof TypeVariableType || sc.getRhs() instanceof TypeVariableType)) {
				/* We have the simple situation where we are saying that a concrete simple type
				 * should be a subtype of another concrete simple type.
				 */
				if(!sc.getLhs().isSubtype(sc.getRhs())) {
					return new SubtypingError(sc.getLhs().name(),sc.getRhs().name());
				}
				return null;
			}
		}
		
		if(!rep.containsKey(sc.getLhs())) {
			rep.put(sc.getLhs(),sc.getLhs());
		}
		if(!rep.containsKey(sc.getRhs())) {
			rep.put(sc.getRhs(),sc.getRhs());
		}
		
		Type s = find(sc.getLhs());
		Type t = find(sc.getRhs());
		
		if (s instanceof TypeVariableType && t instanceof NumericType) {
			return unifySubtype((TypeVariableType) s, (NumericType) t);
		} else if (t instanceof TypeVariableType && s instanceof NumericType) {
			return unifySubtype((NumericType)s, (TypeVariableType) t);
		} else {
			equalityConstraints.add(new EqualityConstraint(s,t,sc.getLine()));
			return null;
		}
	}

	protected Error unifySubtype(NumericType s, TypeVariableType x) {

		/* We have s<:x, where s is a numeric type */
		
		if (s.isSubtype(x.getLower())) {
			return null;
		}
		
		Assert.assertTrue(x.getLower().isSubtype(s));

		if (s.isSubtype(x.getUpper())) {
			x.setLower(s);
			return null;
		}

		return new SubtypingError(s.name(),x.getUpper().name());

	}

	protected Error unifySubtype(TypeVariableType x, NumericType s) {

		if (x.getUpper().isSubtype(s)) {
			return null;
		}
		
		Assert.assertTrue(s.isSubtype(x.getUpper()));
		
		if (x.getLower().isSubtype(s)) {
			x.setUpper(s);
			return null;
		}

		return new SubtypingError(applySubstitutionsAndMinimise(x.getLower()).name(),
				s.name());

	}
	
	protected Error unifyConstraint(Type left, Type right) {

		Type s = find(left);
		Type t = find(right);

		if(s==t) {
			return null;
		}

		if (s instanceof TypeVariableType || t instanceof TypeVariableType) {
			return union(s, t);
		}

		if(s instanceof SimpleType && t instanceof SimpleType) {
			return unifyConstraintOnSimpleTypes((SimpleType)s, (SimpleType)t);
		}
		
		if (s instanceof ChanType && t instanceof ChanType) {
			union(s,t);
			return (unifyConstraint(((ChanType)s).getMessageType(), ((ChanType)t).getMessageType()));
		}

		if (s instanceof ArrayType && t instanceof ArrayType) {
			if(((ArrayType)s).getLength()!=((ArrayType)t).getLength()) {
				return new IncompatibleTypesError(applySubstitutionsAndMinimise(s).name(),applySubstitutionsAndMinimise(t).name());
			}
			Error result = unifyConstraint(((ArrayType)s).getElementType(),
					((ArrayType)t).getElementType());
			if (result == null) {
				union(s,t);
				result = unifyConstraint(((ArrayType)s).getIndexType(), ((ArrayType)t).getIndexType());
			}
			return result;
		}

		if (s instanceof ProductType && t instanceof ProductType) {
			if (((ProductType) s).getArity()==((ProductType) t).getArity()) {
				union(s,t);
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

	protected Error unifyConstraintOnSimpleTypes(SimpleType s, SimpleType t) {
		if(s instanceof MtypeType && t instanceof MtypeType) {
			return null;
		}

		if(s.isSubtype(new BoolType()) && t.isSubtype(new BoolType())) {
			unifyBooleanSubtypes(s, t);
			return null;
		}
		
		if(s instanceof RecordType && t instanceof RecordType && s.equal(t)) {
			return null;
		}

		if(s instanceof ByteType && t instanceof ByteType) {
			unifyByteTypes((ByteType)s, (ByteType)t);
			return null;
		}
		
		if(s instanceof ShortType && t instanceof ShortType) {
			return null;
		}
		
		if(s instanceof IntType && t instanceof IntType) {
			return null;
		}

		return new IncompatibleTypesError(s.name(), t.name());
	
	}

	protected void unifyByteTypes(ByteType s, ByteType t) {

	}

	protected void unifyBooleanSubtypes(Type s, Type t) {

	}

	protected Type find(Type t) {
		if(!rep.containsKey(t)) {
			rep.put(t,t);
			return t;
		}
		Type previous = t;
		Type current = rep.get(t);
		while(current != previous) {
			previous = current;
			current = rep.get(previous);
		}
		return current;
	}

	private Error union(Type s, Type t) {
		// s and t are assumed to be equivalence class representatives

		if(!(s instanceof TypeVariableType || t instanceof TypeVariableType)) {
			rep.put(s,t);
			return null;
		}
		
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
			Type newUpper = leastUpperBound(s,t);
			Type newLower = greatestLowerBound(s,t);

			if (!newLower.isSubtype(newUpper)) {
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

	protected Error checkBounds(TypeVariableType s, Type t) {
		
		if (!s.getLower().isSubtype(t)) {
			return new SubtypingError(s.getLower().name(), applySubstitutionsAndMinimise(t).name());
		} 
		
		if (!t.isSubtype(s.getUpper())) {
			return new SubtypingError(applySubstitutionsAndMinimise(t).name(), s.getUpper().name());
		}
		
		return null;

	}

	private Type applySubstitutionsAndMinimise(Type t) {
		return Minimiser.minimise(new Substituter(this).applySubstitutions(t));
	}

	protected Type greatestLowerBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		return AnyType.max(s.getLower(), t.getLower());
	}

	protected Type leastUpperBound(TypeVariableType s, TypeVariableType t) throws IncomparableTypesException {
		return AnyType.min(s.getUpper(), t.getUpper());
	}
	
	public String toString() {
		String result = "";
		for (Type tv : rep.keySet()) {
			result = result + tv.name() + " |-> " + rep.get(tv).name() + ";\n";
		}
		return result;		
	}

}