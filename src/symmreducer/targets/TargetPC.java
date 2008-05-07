package src.symmreducer.targets;

public class TargetPC extends Target {

	@Override
	public int alignmentValue() {
		return 16;
	}

	static final int size = 16;
	
	public String getSplatsInstruction(String dest, String source) {
		String result = "      ";
		for(int i=0; i<size; i++) {
			result += dest + ".data[" + i + "] = " + source + ";\n      ";
		}
		return result + "\n";
	}

	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		String result = "      ";
		for(int i=0; i<size; i++) {
			result += dest + ".data[" + i + "] = (" + source1 + ".data[" + i + "] == " + source2 + ".data[" + i + "]) ? 1 : 0;\n      ";
		}
		return result + "\n";
	}
	
	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		String result = "      ";
		for(int i=0; i<size; i++) {
			result += dest + ".data[" + i + "] = (" + condition + ".data[" + i + "] == 1) ? " + resultOne + ".data[" + i + "]" + " : " + resultZero + ".data[" + i + "]" + ";\n      ";
		}
		return result + "\n";
	}

	@Override
	public String getVectorUnsignedCharTypename() {
		return "vec_uchar";
	}

	@Override
	public String getVectorUnsignedCharDefinition() {
		String result = "typedef struct vec_uchar_s {\n";
		result += "   uchar data[16];\n";
		result += "} vec_uchar;\n\n";
		return result;
	}

	@Override
	public String getVectorBoolCharTypename() {
		return "vec_uchar";
	}
	
}
