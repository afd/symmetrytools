package src.etch.unifier;

import java.util.*;

import src.etch.checker.Checker;
import src.etch.env.ChannelEntry;
import src.etch.env.VarEntry;
import src.etch.types.Type;
import src.etch.types.TypeSubstituter;
import src.promela.analysis.*;
import src.promela.node.Node;
import src.promela.node.TName;

public class Substituter extends DepthFirstAdapter {

	private TypeGraph graph;

	private Checker nodeTypes;

	public Substituter(TypeGraph graph) {
		this.graph = graph;
	}

	public String toString() {
		return graph.toString();
	}

	public void setTypeInformation(Checker nodeTypes) {
		this.nodeTypes = nodeTypes;
		nodeTypes.getEnv().applySubsitutions(new TypeSubstituter(graph));		
	}

	public void caseTName(TName node) {
		if(nodeTypes.getEnvEntry(node.getText()) instanceof ChannelEntry) {
			VarEntry entry = (VarEntry) nodeTypes.getEnvEntry(node.getText());
			Type newType = new TypeSubstituter(graph).applySubstitutions(entry.getType());
			entry.setType(newType);
		}
	}
	
	@SuppressWarnings("unchecked")
	public void defaultOut(Node node) {
		if (nodeTypes.getOut(node) instanceof Type) {
			nodeTypes.setOut(node,new TypeSubstituter(graph).applySubstitutions((Type) nodeTypes.getOut(node)));
		}
		
		if (nodeTypes.getOut(node) instanceof List) {
			setOut(node,substituteTypeList((List<Type>)nodeTypes.getOut(node)));
		}
	}

	private List substituteTypeList(List<Type> list) {
		List<Type> newValue = new ArrayList<Type>();
		for(int i=0; i<list.size(); i++) {
			newValue.add(new TypeSubstituter(graph).applySubstitutions(list.get(i)));
		}
		return newValue;
	}
	
}
