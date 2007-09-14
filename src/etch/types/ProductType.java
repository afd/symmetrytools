package src.etch.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import junit.framework.Assert;

public class ProductType extends ConstructedType implements InternalType {

	List<Type> tuple;

	public ProductType(List<Type> tuple) {
		this.tuple = new ArrayList<Type>(tuple.size());
		for(int i=0; i<tuple.size(); i++) {
			Assert.assertFalse(tuple.get(i) instanceof ProductType);
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
		Assert.assertFalse(t instanceof ProductType);
		tuple.set(i,t);
	}
	
	public int getArity() {
		return tuple.size();
	}

	protected String namePlugin(TypeVariableFactory factory) {
		String result = "{ ";
		ListIterator<Type> i = tuple.listIterator();
		while (i.hasNext()) {
			Type t = i.next();
			if(t instanceof SimpleType) {
				result = result + t.name();
			} else {
				result = result + ((ConstructedType)t).nameRecursive(factory);
			}
			if (i.hasNext()) {
				result = result + ", ";
			}
		}
		result = result + " }";
		return result;
	}

	protected void replaceChildWithTypeVariable(ConstructedType type, TypeVariableType tVar) {
		boolean madeAReplacement = false;
		for(int i=0; i<tuple.size(); i++) {
			if(tuple.get(i) == type) {
				tuple.set(i,tVar);
				madeAReplacement = true;
			}
		}
		Assert.assertTrue(madeAReplacement);
	}

	protected Set<ConstructedType> computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(ConstructedType type, Set<ConstructedType> alreadyVisited) {
		Set<ConstructedType> result = new HashSet<ConstructedType>();
		if(alreadyVisited.contains(this)) {
			// We've already checked this node
			return result;
		}
		
		// Mark this node as checked
		alreadyVisited.add(this);
		
		for(Type t : tuple) {
			if(t instanceof ConstructedType) {
				if(t == type) {
					result.add(this);
				} else {
					result.addAll(((ConstructedType)t).computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(type,alreadyVisited));
				}
			}
		}
		return result;
	}

	protected ConstructedType cloneAndUnrollPlugin(Map<ConstructedType, ConstructedType> cloneMap) {

		List<Type> nullTypeList = new ArrayList<Type>();
		for(int i=0; i<tuple.size(); i++) {
			nullTypeList.add(null);
		}

		ProductType clonedProduct = new ProductType(nullTypeList);

		cloneMap.put(this,clonedProduct);
		
		for(int i=0; i<tuple.size(); i++) {
			if(getTypeOfPosition(i) instanceof SimpleType) {
				clonedProduct.setTypeOfPosition(i,getTypeOfPosition(i));
			} else {
				Map<ConstructedType,ConstructedType> newCloneMap = new HashMap<ConstructedType,ConstructedType>(cloneMap);
				clonedProduct.setTypeOfPosition(i,((ConstructedType)getTypeOfPosition(i)).cloneAndUnroll(newCloneMap));
			}
		}
		
		return clonedProduct;
			
	}

	public ListIterator<Type> getElementIterator() {
		return tuple.listIterator();
	}

}