package src.etch.types;

public interface Type {

	public String name();	

	public boolean equal(Type t);

	public boolean isSubtype(Type t);

}
