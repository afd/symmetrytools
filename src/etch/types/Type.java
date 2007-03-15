package src.etch.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

public abstract class Type {

	protected static int noProcesses;
	private static boolean checkingSymmetry = false;

	public String name() {
		List<String> nameComponents = computeNameComponents(this,new TypeVariableFactory('Y'),new HashMap<Type,Integer>(),new HashMap<Type,TypeVariableType>(), new ArrayList<String>());
		
		String result = "";
		for(String s : nameComponents) {
			result += s;
		}
		return result;
	}

	public boolean equal(Type t) {
		return Minimiser.minimise(t).name().equals(Minimiser.minimise(this).name());
	}

	public static void setCheckingSymmetry(boolean isPidSensitive) {
		checkingSymmetry = isPidSensitive;
	}

	public static void setNoProcesses(int noProcesses) {
		Type.noProcesses = noProcesses;
	}
	
	public abstract boolean isSubtype(Type t);

	public static boolean checkingSymmetry() {
		return checkingSymmetry;
	}

	public static int noProcesses() {
		return noProcesses;
	}
	
	public static Type max(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t2;
		} else if (t2.isSubtype(t1)) {
			return t1;
		} else {
			throw new IncomparableTypesException(t1, t2);
		}
	}
	
	public static Type min(Type t1, Type t2) throws IncomparableTypesException {
		if (t1.isSubtype(t2)) {
			return t1;
		} else if (t2.isSubtype(t1)) {
			return t2;
		} else {
			throw new IncomparableTypesException(t1, t2);
		}
	}
	
	public void setNotPidLiteral() {
		// This method is overridden by certain subclasses.  It intentionally does nothing
		// for most Type classes.
	}

	private List<String> computeNameComponents(Type type, TypeVariableFactory factory, Map<Type, Integer> typeToStringPosition, Map<Type, TypeVariableType> typeToTypeVariable, List<String> names) {

		if(type instanceof SimpleType) {
			names.add(type.name());
			return names;
		}

		if(typeToStringPosition.get(type)!=null) {
			int stringPosition = typeToStringPosition.get(type);
			if(typeToTypeVariable.get(type)!=null) {
				TypeVariableType tvar = typeToTypeVariable.get(type);
				names.add(tvar.name());
				return names;
			} else {
				TypeVariableType tvar = factory.freshTypeVariable();
				typeToTypeVariable.put(type,tvar);
				names.set(stringPosition,"rec " + tvar.name() + " . " + names.get(stringPosition));
				names.add(tvar.name());
				return names;
			}
			
		} else {
			typeToStringPosition.put(type,names.size());
			
			if(type instanceof ArrayType) {
				names.add("");
				names = computeNameComponents(((ArrayType)type).getElementType(),factory,typeToStringPosition,typeToTypeVariable,names);
				names.add("[" + ((ArrayType)type).getIndexType().name() + "," + ((ArrayType)type).getLength() + "]");
				return names;
			}
			
			if(type instanceof ChanType) {
				names.add("chan ");
				names = computeNameComponents(((ChanType)type).getMessageType(),factory,typeToStringPosition,typeToTypeVariable,names);
				return names;
			}
			
			if(type instanceof ProductType) {
				names.add("{");
				for(int i=0; i<((ProductType)type).getArity(); i++) {
					names = computeNameComponents(((ProductType)type).getTypeOfPosition(i),factory,typeToStringPosition,typeToTypeVariable,names);
					if(i<((ProductType)type).getArity()-1) {
						names.add(", ");
					}
				}
				
				names.add("}");
				return names;
			}
			
			Assert.assertTrue(false);
			return null;
			
		}
	
	}
	
	public String toString() {
		return name();
	}

}
