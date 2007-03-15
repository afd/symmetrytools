package src.etch.types;

import java.util.*;

public class ProductType extends Type {

	List<Type> tuple;

	public ProductType(List<Type> tuple) {
		this.tuple = new ArrayList<Type>(tuple.size());
		for(int i=0; i<tuple.size(); i++) {
			this.tuple.add(tuple.get(i));
		}
	}
	
	public Type getTypeOfPosition(int i) {
		return ((Type) tuple.get(i));
	}

	protected void setTypeOfPosition(int i, Type t) {
		tuple.set(i,t);
	}
	
	public int getArity() {
		return tuple.size();
	}

	public String name() {
		String result = "{";
		ListIterator i = tuple.listIterator();
		while (i.hasNext()) {
			result = result + ((Type) i.next()).name();
			if (i.hasNext()) {
				result = result + ",";
			}
		}
		result = result + "}";
		return result;
	}

	public boolean isSubtype(Type t) {
		return equal(t);
	}

}
