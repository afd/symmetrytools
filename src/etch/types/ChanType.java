package src.etch.types;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.Assert;

public class ChanType extends ConstructedType implements VisibleType {

	private InternalType messageType;

	public ChanType(InternalType messageType) {
		Assert.assertTrue(messageType == null || messageType instanceof ProductType || messageType instanceof TypeVariableType);
		this.messageType = messageType;
	}

	public ChanType(List<Type> messageFieldTypes) {
		this.messageType = new ProductType(messageFieldTypes);
	}

	protected ChanType() {
		this.messageType = null;
	}

	public InternalType getMessageType() {
		return messageType;
	}
	
	public void setMessageType(InternalType t) {
		/* Unfortunately this needs to be public, as it
		 * is called by the Substituter class which is in
		 * a different package (as it really should be) 
		 * */
		messageType = t;
	}
	
	protected String namePlugin(TypeVariableFactory factory) {
		String result = "chan ";
		if(messageType instanceof SimpleType) {
			return result + messageType.name();
		}
		return result + ((ConstructedType)messageType).nameRecursive(factory);
	}

	protected void replaceChildWithTypeVariable(ConstructedType type, TypeVariableType tVar) {
		Assert.assertTrue(messageType == type);
		messageType = tVar;
	}

	protected Set<ConstructedType> computeDescendentsOfTypeWhichAreAlsoDirectPredecessors(ConstructedType type, Set<ConstructedType> alreadyVisited) {
		Set<ConstructedType> result = new HashSet<ConstructedType>();
		if(alreadyVisited.contains(this)) {
			// We've already checked this node
			return result;
		}
		
		// Mark this node as checked
		alreadyVisited.add(this);

		if(messageType instanceof ConstructedType) {
			if(messageType == type) {
				result.add(this);
			} else {
				result.addAll(((ConstructedType)messageType).computeDescendentsOfTypeWhichAreAlsoDirectPredecessors((ConstructedType) type,alreadyVisited));
			}
		}
		
		return result;
	}

	public static boolean isChan(VisibleType t) {
		return t instanceof ChanType;
	}

	public static boolean containsChanType(List<VisibleType> typeList) {
		for (VisibleType vt : typeList) {
			if (isChan(vt)) {
				return true;
			}
		}
		return false;
	}

	
	public static int getNumberOfChanTypes(List<VisibleType> typeList) {
		int result = 0;
		for(VisibleType vt : typeList) {
			if(isChan(vt)) {
				result++;
			}
		}
		return result;
	}
	
}
