package src.symmreducer.vectortargets;

public class CellSPUVectorTarget implements VectorTarget {

	public int alignmentValue() {
		return 16;
	}

	public String getSplatsInstruction(String dest, String source) {
		return "spu_splats";
	}

	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		return "spu_cmpeq";
	}

	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		return "spu_sel";
	}

	public String getVectorUnsignedCharDefinition() {
		return "";
	}

	public String getVectorUnsignedCharTypename() {
		return "vector unsigned char";
	}

	public String getVectorBoolCharTypename() {
		return "vector bool char";
	}

}
