package src.etch.types;

import java.util.List;


import src.etch.checker.Checker;

public class ChanType extends ConstructedType implements VisibleType {

	private InternalType messageType;

	public ChanType(InternalType messageType) {
		assert(messageType == null || messageType instanceof ProductType || messageType instanceof TypeVariableType);
		this.messageType = messageType;
	}

	public ChanType(List<Type> messageFieldTypes) {
		this.messageType = Checker.theFactory.generateProductType(messageFieldTypes);
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

	public void nameComponentsDFS(TypeStack stack, List<String> result) {
		
		result.add("chan ");
		
		if(stack.push(messageType,result)) {
			messageType.nameComponentsDFS(stack,result);
			stack.pop();
		}
	}

}
