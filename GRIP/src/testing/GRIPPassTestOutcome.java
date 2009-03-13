package src.testing;

import src.translator.ModelType;

public class GRIPPassTestOutcome implements GRIPTestOutcome {

	private ModelType modelType;

	private long numberOfBDDNodes;
	
	private long numberOfStates;

	private long numberOfTransitions;
	
	private long numberOfChoices;
	
	public GRIPPassTestOutcome(ModelType modelType, long numberOfBDDNodes, long numberOfStates, long numberOfTransitions, long numberOfChoices) {
		this.modelType = modelType;
		this.numberOfBDDNodes = numberOfBDDNodes;
		this.numberOfStates = numberOfStates;
		this.numberOfTransitions = numberOfTransitions;
		this.numberOfChoices = numberOfChoices;
		
		if(this.modelType == ModelType.stochastic) {
			assert(this.numberOfChoices == -1);
		}
	}
	
	public boolean matches(TestOutcome actualOutcome) {
		return (actualOutcome instanceof GRIPPassTestOutcome) && equal((GRIPPassTestOutcome)actualOutcome);
	}

	private boolean equal(GRIPPassTestOutcome outcome) {
		return (modelType == outcome.modelType) &&
		        (numberOfBDDNodes == outcome.numberOfBDDNodes) &&
				(numberOfStates == outcome.numberOfStates) &&
				(numberOfTransitions == outcome.numberOfTransitions) &&
				(numberOfChoices == outcome.numberOfChoices);
	}

	public String toString() {
		return "(type: " + modelType + ", nodes: " + numberOfBDDNodes + ", states: " + numberOfStates + ", transitions: " + numberOfTransitions + ", choices: " + numberOfChoices + ")";
	}

}
