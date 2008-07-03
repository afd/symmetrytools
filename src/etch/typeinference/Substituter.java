package src.etch.typeinference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;
import src.etch.checker.Checker;
import src.etch.env.ChannelEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ChanType;
import src.etch.types.InternalType;
import src.etch.types.ProductType;
import src.etch.types.SimpleType;
import src.etch.types.Type;
import src.etch.types.TypeVariableType;
import src.etch.types.VisibleType;
import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.Node;
import src.promela.node.TName;

public class Substituter extends DepthFirstAdapter {

	private Unifier graph;

	private Checker nodeTypes;

	public Substituter(Unifier graph) {
		this.graph = graph;
	}

	public String toString() {
		return graph.toString();
	}

	public Type applySubstitutions(Type t) {
		return applySubstitutionsRecursive(t,new HashMap<Type,Type>());
	}

	private Type applySubstitutionsRecursive(Type t, Map<Type,Type> history) {

		if(history.get(t)!=null)
		{
			return history.get(t);
		}
		
		Type tRep = graph.find(t);

		if(tRep instanceof SimpleType) {
			return tRep;
		}

		if (tRep instanceof ArrayType) {
			ArrayType result = Checker.theFactory.generateArrayType(null,null,((ArrayType)tRep).getLength());
			history.put(t,result);
			result.setElementType((VisibleType) applySubstitutionsRecursive(((ArrayType)tRep).getElementType(),history));
			Type newIndexType = applySubstitutionsRecursive(((ArrayType)tRep).getIndexType(),history);
			if(newIndexType instanceof TypeVariableType) {
				// Substitute the type variable with byte by default
				result.setIndexType(Checker.theFactory.generateByteType());
			} else if(newIndexType instanceof SimpleType) {
				result.setIndexType((SimpleType)newIndexType);
			} else {
				Assert.assertTrue(false);
			}
			return result;
		} 
		
		if (tRep instanceof ChanType) {
			ProductType messageType = null;
			ChanType result = new ChanType(messageType);
			history.put(t,result);
			result.setMessageType((InternalType) applySubstitutionsRecursive(((ChanType)tRep).getMessageType(),history));
			return result;
		}

		if (tRep instanceof ProductType) {
			List<Type> tuple = new ArrayList<Type>();
			for(int i=0; i<((ProductType)tRep).getArity(); i++) {
				tuple.add(null);
			}
			ProductType result = Checker.theFactory.generateProductType(tuple);

			history.put(t,result);
			for(int i=0; i<((ProductType)tRep).getArity(); i++) {
				result.setTypeOfPosition(i,applySubstitutionsRecursive(((ProductType)tRep).getTypeOfPosition(i),history));
			}
			return result;
		}
		
		Assert.assertTrue(false);
		return null;
	}
	

	
	
	
	
	public void setTypeInformation(Checker nodeTypes) {
		this.nodeTypes = nodeTypes;
		nodeTypes.getEnv().applySubsitutions(this);		
	}

	public void caseTName(TName node) {
		if(nodeTypes.getEnvEntry(node.getText()) instanceof ChannelEntry) {
			VarEntry entry = (VarEntry) nodeTypes.getEnvEntry(node.getText());
			Type newType = applySubstitutions(entry.getType());
			Assert.assertTrue(newType instanceof VisibleType);
			entry.setType((VisibleType) newType);
		}
	}
	
	@SuppressWarnings("unchecked")
	public void defaultOut(Node node) {
		if (nodeTypes.getOut(node) instanceof Type) {
			nodeTypes.setOut(node, applySubstitutions((Type) nodeTypes.getOut(node)));
		}
		
		if (nodeTypes.getOut(node) instanceof List) {
			setOut(node,substituteTypeList((List<Type>)nodeTypes.getOut(node)));
		}
	}

	private List substituteTypeList(List<Type> list) {
		List<Type> newValue = new ArrayList<Type>();
		for(int i=0; i<list.size(); i++) {
			newValue.add(applySubstitutions(list.get(i)));
		}
		return newValue;
	}
	
}
