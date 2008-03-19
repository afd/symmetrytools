package src.symmreducer.targets;

public abstract class Target {

	public abstract int alignmentValue();

	public boolean requiresAlignment() {
		return alignmentValue() > 1;
	}

	public abstract String getSplatsInstruction(String dest, String source);

	public abstract String getCompareEqualInstruction(String dest, String source1, String source2);
	
	public abstract String getSelectInstruction(String dest, String condition, String resultOne, String resultZero);

	public abstract String getVectorUnsignedCharDefinition();

	public abstract String getVectorUnsignedCharTypename();

	public abstract String getVectorBoolCharTypename();
	
}
