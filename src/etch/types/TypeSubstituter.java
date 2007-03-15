package src.etch.types;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.Assert;

import src.etch.unifier.TypeGraph;

public class TypeSubstituter {

	private TypeGraph typeGraph;
	
	public TypeSubstituter(TypeGraph typeGraph) {
		this.typeGraph = typeGraph;
	}

	public Type applySubstitutions(Type t) {
		return applySubstitutionsRecursive(t,new HashSet<Type>());
	}

	private Type applySubstitutionsRecursive(Type t, Set<Type> history) {
		
		Type tRep = typeGraph.rep(t);

		if(tRep instanceof SimpleType || history.contains(tRep)) {
			return tRep;
		}
		
		if (tRep instanceof ArrayType) {
			ArrayType result = new ArrayType(null,null,((ArrayType)tRep).getLength());
			history.add(result);
			result.setElementType(applySubstitutionsRecursive(((ArrayType)tRep).getElementType(),history));
			Type newIndexType = applySubstitutionsRecursive(((ArrayType)tRep).getIndexType(),history);
			if(newIndexType instanceof TypeVariableType) {
				// Substitute the type variable with byte by default
				result.setIndexType(new ByteType());
			} else if(newIndexType instanceof SimpleType) {
				result.setIndexType((SimpleType)newIndexType);
			} else {
				Assert.assertTrue(false);
			}
			return result;
		} 
		
		if (tRep instanceof ChanType) {
			ProductType messageType = null;
			ChanType result = new ChanType(messageType);
			history.add(result);
			result.setMessageType(applySubstitutionsRecursive(((ChanType)tRep).getMessageType(),history));
			return result;
		}

		if (tRep instanceof ProductType) {
			List<Type> tuple = new ArrayList<Type>();
			for(int i=0; i<((ProductType)tRep).getArity(); i++) {
				tuple.add(null);
			}
			ProductType result = new ProductType(tuple);
			history.add(result);
			for(int i=0; i<((ProductType)tRep).getArity(); i++) {
				result.setTypeOfPosition(i,applySubstitutionsRecursive(((ProductType)tRep).getTypeOfPosition(i),history));
			}
			return result;
		}
		
		Assert.assertTrue(false);
		return null;
	}
}
