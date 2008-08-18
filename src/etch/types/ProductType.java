package src.etch.types;

import java.util.ArrayList;
import java.util.List;



public class ProductType extends ConstructedType implements InternalType {

	List<Type> tuple;

	public ProductType(List<Type> tuple) {
		this.tuple = new ArrayList<Type>(tuple.size());
		for(int i=0; i<tuple.size(); i++) {
			assert(!(tuple.get(i) instanceof ProductType));
			/* Could also do an assert on array types, as Promela doesn't
			 * allow arrays to be passed on channels.  Currently, Etch
			 * won't complain about this though.
			 */
			this.tuple.add(tuple.get(i));
		}
	}
	
	public Type getTypeOfPosition(int i) {
		return tuple.get(i);
	}

	public void setTypeOfPosition(int i, Type t) {
		assert(!(t instanceof ProductType));
		tuple.set(i,t);
	}
	
	public int getArity() {
		return tuple.size();
	}

	public void nameComponentsDFS(TypeStack stack, List<String> result) {
		
		result.add("{ ");
		
		for(int i=0; i<getArity(); i++) {
			Type typeOfPosition = getTypeOfPosition(i);
			if(stack.push(typeOfPosition,result)) {
				typeOfPosition.nameComponentsDFS(stack,result);
				stack.pop();
			}
			if(i<getArity()-1) {
				result.add(", ");
			}
		}
		result.add(" }");
		
		
	}

}