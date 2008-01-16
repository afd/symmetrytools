package src.etch.types;

import java.util.HashSet;
import java.util.Set;

public abstract class ConstructedType extends AnyType {

	public final boolean isSubtype(Type t) {
		return equal(t);
	}

	protected abstract String namePlugin(TypeVariableFactory factory);

	public boolean equal(Type t) {
		return t instanceof ConstructedType &&
		 ((ConstructedType)t).minimisedName().equals(this.minimisedName());
	}

	private String minimisedName() {
		return Minimiser.minimise(this).name();
	}

	public final String name() {
		return super.name();
	}
	
	/* Display the name of the type, recursively.
	 * Note that, in its current form, this method actually
	 * modifies the type.  It might be best to write a clone
	 * method, and to display the (identical) name of the
	 * cloned type.
	 */
	protected String nameRecursive(TypeVariableFactory factory) {
		
		TypeVariableType tVar = introduceTypeVariablesForCycles(factory);

		String result = "";

		if(tVar != null) {
			result += "rec " + tVar.name() + " . ";
		}

		result += this.namePlugin(factory);

		return result;
	}

	private TypeVariableType introduceTypeVariablesForCycles(TypeVariableFactory factory) {
		Set<ConstructedType> descendantsOfThisWhichAreAlsoPredecessors = computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(this, new HashSet<ConstructedType>());
		if(descendantsOfThisWhichAreAlsoPredecessors.isEmpty()) {
			return null;
		}
		TypeVariableType tVar = factory.freshTypeVariable();
		
		
		for(ConstructedType cType: descendantsOfThisWhichAreAlsoPredecessors) {
			cType.replaceChildWithTypeVariable(this,tVar);
		}

		return tVar;
	}

	protected abstract void replaceChildWithTypeVariable(ConstructedType type, TypeVariableType tVar);

	protected abstract Set<ConstructedType> computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(ConstructedType type, Set<ConstructedType> alreadyVisited);
	
}
