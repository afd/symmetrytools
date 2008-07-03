package src.etch.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


import junit.framework.Assert;

public class TypeStack {

	private List<Type> stack;
	
	private Map<Type,Integer> typeToNameComponentIndex;
	
	private Map<Type,TypeVariableType> typeToTypeVariable;

	private TypeVariableFactory factory;
	
	public TypeStack(AnyType type) {
		stack = new ArrayList<Type>();
		typeToNameComponentIndex = new HashMap<Type,Integer>();
		typeToTypeVariable = new HashMap<Type,TypeVariableType>();
		factory = new TypeVariableFactory('Y',true);
		
		stack.add(type);
		typeToNameComponentIndex.put(type,0);
	}

	public void pop() {
		Type t = stack.remove(stack.size()-1);
		typeToNameComponentIndex.remove(t);
		typeToTypeVariable.remove(t);
	}

	public boolean push(Type t, List<String> nameComponents) {
		if(stack.contains(t)) {
			Assert.assertFalse(t instanceof ArrayType);

			if(typeToTypeVariable.containsKey(t)) {
				nameComponents.add(typeToTypeVariable.get(t).name());
			} else {
				int nameComponentIndex = typeToNameComponentIndex.get(t);
				TypeVariableType tv = factory.freshTypeVariable();
				nameComponents.set(nameComponentIndex,"rec " + tv.name() + " . " + nameComponents.get(nameComponentIndex));
				nameComponents.add(tv.name());
				typeToTypeVariable.put(t,tv);
			}
			return false;
		}
		
		stack.add(t);
		typeToNameComponentIndex.put(t, nameComponents.size());		
		return true;
	}

}
