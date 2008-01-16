package src.etch.types;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import src.etch.checker.SymmetrySettings;
import src.etch.error.IncomparableTypesException;

public abstract class AnyType implements Type {

/*	public String toString() {
		return name();
	}*/

	public static Type max(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t2;
		} else if (t2.isSubtype(t1)) {
			return t1;
		}
		/* Throw an exception if the types are incomparable */
		throw new IncomparableTypesException(t1,t2);
	}

	public static Type min(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t1;
		} else if (t2.isSubtype(t1)) {
			return t2;
		}
		/* Throw an exception if the types are incomparable */
		throw new IncomparableTypesException(t1,t2);
	}
	
	public String name() {
		List<String> nameComponents = new ArrayList<String>();
		nameComponentsDFS(new TypeStack(this),nameComponents);
		String result = "";
		for(String component : nameComponents) {
			result += component;
		}
		return result;
	}

	public void nameComponentsDFS(TypeStack stack, List<String> result) {
		
		if(this instanceof SimpleType) {
			result.add(this.name());
			return;
		} 
		
		if(this instanceof ArrayType) {
			String component = "array(size " + ((ArrayType)this).getLength();
			
			if(SymmetrySettings.CHECKING_SYMMETRY && !(((ArrayType)this).getIndexType() instanceof TypeVariableType)) {
				component += ", indexed by " + ((ArrayType)this).getIndexType().name();
			}

			component += ") of ";

			result.add(component);

			VisibleType elementType = ((ArrayType)this).getElementType();
			if(stack.push(elementType,result)) {
				elementType.nameComponentsDFS(stack,result);
				stack.pop();
			}

			return;
		}
		
		
		if(this instanceof ChanType) {
			InternalType messageType = ((ChanType)this).getMessageType();
			
			result.add("chan ");
			
			if(stack.push(messageType,result)) {
				messageType.nameComponentsDFS(stack,result);
				stack.pop();
			}

			return;
		}

		Assert.assertTrue(this instanceof ProductType);
		
		result.add("{ ");
		
		for(int i=0; i<((ProductType)this).getArity(); i++) {
			Type typeOfPosition = ((ProductType)this).getTypeOfPosition(i);
			if(stack.push(typeOfPosition,result)) {
				typeOfPosition.nameComponentsDFS(stack,result);
				stack.pop();
			}
			if(i<((ProductType)this).getArity()-1) {
				result.add(", ");
			}
		}
		result.add(" }");
		
	}	
		
		
	
	
	
	
	
}
