package src.etch.types;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;
import src.etch.typeinference.TypeGraph;

public class TypeSubstituter {

	private TypeGraph typeGraph;
	
	public TypeSubstituter(TypeGraph typeGraph) {
		this.typeGraph = typeGraph;
	}

}
