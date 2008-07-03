package src.etch.types;

import java.util.List;

public interface Type {

	public String name();	

	public boolean equal(Type t);

	public boolean isSubtype(Type t);

	public void nameComponentsDFS(TypeStack stack, List<String> result);
	
}
