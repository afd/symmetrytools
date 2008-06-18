package src.symmreducer.vectortargets;

public interface VectorTarget {

	public int alignmentValue();

	public String getSplatsInstruction(String dest, String source);

	public String getCompareEqualInstruction(String dest, String source1, String source2);
	
	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero);

	public String getVectorUnsignedCharDefinition();

	public String getVectorUnsignedCharTypename();

	public String getVectorBoolCharTypename();
	
}
