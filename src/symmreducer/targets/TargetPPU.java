package src.symmreducer.targets;


public class TargetPPU extends Target {

	@Override
	public int alignmentValue() {
		return 16;
	}

	@Override
	public String getSplatsInstruction(String dest, String source) {
		return "      " + dest + " = vec_splats((uchar)" + source + ");\n";
	}

	@Override
	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		return "      " + dest + " = vec_cmpeq(" + source1 + ", " + source2 + ");\n";
	}

	@Override
	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		return "      " + dest + " = vec_sel(" + resultZero + ", " + resultOne + ", " + condition + ");\n";
	}

	@Override
	public String getVectorUnsignedCharTypename() {
		return "vector unsigned char";
	}

	@Override
	public String getVectorBoolCharTypename() {
		return "vector bool char";
	}

	@Override
	public String getVectorUnsignedCharDefinition() {
		return "#include <altivec.h>\n#include <vec_types.h>\n\n";
	}

}
