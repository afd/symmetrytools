package src.etch.types;

import java.util.List;


public abstract class SimpleType extends AnyType {

	public final boolean equal(Type t) {
		return t instanceof SimpleType && name().equals(t.name());
	}
	
	public void nameComponentsDFS(TypeStack stack, List<String> result)
	{
		result.add(this.name());
	}	
	
}
