package src.symmreducer.vectortargets;


public class PowerPCVectorTarget implements VectorTarget {

	private static final int vectorLength = 16;
	
	public int alignmentValue() {
		return vectorLength;
	}

	public String getSplatsInstruction(String dest, String source) {
		return "      " + dest + " = vec_splats((uchar)" + source + ");\n";
	}

	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		return "      " + dest + " = vec_cmpeq(" + source1 + ", " + source2 + ");\n";
	}

	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		return "      " + dest + " = vec_sel(" + resultZero + ", " + resultOne + ", " + condition + ");\n";
	}

	public String getVectorUnsignedCharTypename() {
		return "vector unsigned char";
	}

	public String getVectorBoolCharTypename() {
		return "vector bool char";
	}

	public String getVectorUnsignedCharDefinition() {
		return "#include <altivec.h>\n#include <vec_types.h>\n\n";
	}

}
