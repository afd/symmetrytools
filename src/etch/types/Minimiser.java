package src.etch.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

public class Minimiser {

	public static Type minimise(Type t) {
		List<Type> nodeNumbers = assignNumbers(t,new ArrayList<Type>());
		int[] classes = mark(t, nodeNumbers);
		return minimalForm(t, classes, nodeNumbers, new HashMap<Integer,Type>());
	}

	private static Type minimalForm(Type t, int[] classes, List<Type> nodeNumbers, Map<Integer,Type> previousAssignments) {
		if(t instanceof SimpleType) {
			return t;
		}
		
		int classNo = classes[nodeNumbers.indexOf(t)];

		if(previousAssignments.containsKey(classNo)) {
			return previousAssignments.get(classNo);
		}
		
		Type representativeType = nodeNumbers.get(classNo);
	
		if(representativeType instanceof ArrayType) {
			int length = ((ArrayType)representativeType).getLength();
			SimpleType indexType = ((ArrayType)representativeType).getIndexType();
			
			ArrayType result = new ArrayType(null,indexType,length);
			
			previousAssignments.put(classNo,result);
		
			result.setElementType(minimalForm(((ArrayType)representativeType).getElementType(),classes,nodeNumbers,previousAssignments));

			return result;
		}

		if(representativeType instanceof ChanType) {
			ProductType msgType = null;
			ChanType result = new ChanType(msgType);
			
			previousAssignments.put(classNo,result);
		
			result.setMessageType(minimalForm(((ChanType)representativeType).getMessageType(),classes,nodeNumbers,previousAssignments));

			return result;
		}
		
		if(representativeType instanceof ProductType) {
			List<Type> tuple = new ArrayList<Type>();
			for(int i=0; i<((ProductType)representativeType).getArity(); i++) {
				tuple.add(null);
			}
			
			ProductType result = new ProductType(tuple);

			previousAssignments.put(classNo,result);
		
			for(int i=0; i<((ProductType)representativeType).getArity(); i++) {
				result.setTypeOfPosition(i,minimalForm(((ProductType)representativeType).getTypeOfPosition(i),classes,nodeNumbers,previousAssignments));
			}
			return result;
		}

		
		Assert.assertTrue(false);
		return null;
	}

	private static List<Type> assignNumbers(Type t, List<Type> l) {
		if (l.contains(t) || isSimpleType(t)) {
			return l;
		}
		
		l.add(t);

		if (t instanceof ArrayType) {
			return assignNumbers(((ArrayType) t).getElementType(), l);
		}
		if (t instanceof ChanType) {
			return assignNumbers(((ChanType) t).getMessageType(), l);
		}
		if (t instanceof ProductType) {
			for (int i = 0; i < ((ProductType) t).getArity(); i++) {
				l = assignNumbers(((ProductType) t).getTypeOfPosition(i), l);
			}
			return l;
		}
		
		Assert.assertTrue(false);
		return null;
	}

	private static boolean isSimpleType(Type t) {
		return t instanceof MtypeType || t instanceof NumericType || t instanceof PidType || t instanceof BoolType || t instanceof RecordType || t instanceof TypeVariableType;
	}

	private static int[] mark(Type t, List<Type> nodeNumbers) {
		boolean[][] distinguishable = markImmediatelyDistinguishableNodes(nodeNumbers,t);
		computeFixpointMarking(distinguishable, nodeNumbers, t);
		return assignRepresentatives(distinguishable);
	}

	private static boolean[][] markImmediatelyDistinguishableNodes(List<Type> nodeNumbers, Type top) {
		boolean distinguishable[][] = new boolean[nodeNumbers.size()][nodeNumbers.size()];
		for (int i = 0; i < nodeNumbers.size()-1; i++) {
			for (int j = i+1; j < nodeNumbers.size(); j++) {
				
				Type iType = nodeNumbers.get(i);
				Type jType = nodeNumbers.get(j);
				
				if(iType instanceof ArrayType) {
					distinguishable[i][j] =
						(!(jType instanceof ArrayType)) ||
						(((ArrayType)iType).getLength()!=((ArrayType)jType).getLength()) ||
						(!((ArrayType)iType).getIndexType().equal(((ArrayType)jType).getIndexType())) ||
						((((ArrayType)iType).getElementType() instanceof SimpleType) && !(((ArrayType)jType).getElementType() instanceof SimpleType)) ||
						((((ArrayType)jType).getElementType() instanceof SimpleType) && !(((ArrayType)iType).getElementType() instanceof SimpleType)) ||
						((((ArrayType)iType).getElementType() instanceof SimpleType) && (((ArrayType)jType).getElementType() instanceof SimpleType) && !((ArrayType)iType).getElementType().equal(((ArrayType)jType).getElementType()));
				} else if(iType instanceof ChanType) {
					distinguishable[i][j] = !(jType instanceof ChanType);
				} else if(iType instanceof ProductType) {
					if((!(jType instanceof ProductType)) || ((ProductType)iType).getArity()!=((ProductType)jType).getArity()) {
						distinguishable[i][j] = true;
					} else {
						distinguishable[i][j] = false;
						
						for(int k=0; k<((ProductType)iType).getArity(); k++) {

							Type iTypek = ((ProductType)iType).getTypeOfPosition(k);
							Type jTypek = ((ProductType)jType).getTypeOfPosition(k);

							if(iTypek instanceof SimpleType) {
								if(!(jTypek instanceof SimpleType)) {
									distinguishable[i][j] = true;
									break;
								} else {
									if(!(iTypek.equal(jTypek))) {
										distinguishable[i][j] = true;
										break;
									}
								}
							} else {
								if(jTypek instanceof SimpleType) {
									distinguishable[i][j] = true;
									break;
								}
							}
						}
										
					}
				
				} else {
					Assert.assertTrue(false);
				}
				
			}
		}
				
		return distinguishable;
	}

	private static void computeFixpointMarking(boolean[][] distinguishable, List<Type> nodeNumbers, Type t) {
		boolean changedInLastPhase = true;
		while (changedInLastPhase) {
			changedInLastPhase = false;
			for (int i = 0; i < nodeNumbers.size()-1; i++) {
				for (int j = i + 1; j < nodeNumbers.size(); j++) {
					if (!distinguishable[i][j]) {

						
						Type iType = nodeNumbers.get(i);
						Type jType = nodeNumbers.get(j);

						if(iType instanceof ArrayType) {
							int k = nodeNumbers.indexOf(((ArrayType)iType).getElementType());
							int l = nodeNumbers.indexOf(((ArrayType)jType).getElementType());
							distinguishable[i][j] = (k<l?distinguishable[k][l]:distinguishable[l][k]);
						} else if(iType instanceof ChanType) {
							int k = nodeNumbers.indexOf(((ChanType)iType).getMessageType());
							int l = nodeNumbers.indexOf(((ChanType)jType).getMessageType());
							distinguishable[i][j] = (k<l?distinguishable[k][l]:distinguishable[l][k]);
						} else if(iType instanceof ProductType) {
							for(int m=0; m<((ProductType)iType).getArity(); m++) {
								if(!(((ProductType)iType).getTypeOfPosition(m) instanceof SimpleType)) {
									int k = nodeNumbers.indexOf(((ProductType)iType).getTypeOfPosition(m));
									int l = nodeNumbers.indexOf(((ProductType)jType).getTypeOfPosition(m));
									distinguishable[i][j] = (k<l?distinguishable[k][l]:distinguishable[l][k]);
									if(distinguishable[i][j]) {
										break;
									}
								}
							}
						} else {
							Assert.assertTrue(false);
						}

						changedInLastPhase = (distinguishable[i][j]?true:changedInLastPhase);
					}
				}
			}
		}
	}
	
	private static int[] assignRepresentatives(boolean[][] distinguishable) {
		int[] representatives = new int[distinguishable.length];
		for (int i = 0; i < representatives.length; i++) {
			representatives[i] = i;
		}
		for (int i = 0; i < representatives.length; i++) {
			for (int j = 0; j < representatives.length; j++) {
				if ((i < j) && (!(distinguishable[i][j])) && (i < representatives[j])) {
					representatives[j] = i;
				} else if ((!(distinguishable[j][i])) && (j < representatives[i])) {
					representatives[i] = j;
				}
			}
		}
		return representatives;
	}

}
