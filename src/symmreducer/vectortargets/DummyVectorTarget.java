package src.symmreducer.vectortargets;

public class DummyVectorTarget implements VectorTarget {

	private static final int vectorLength = 16;

	public int alignmentValue() {
		return vectorLength;
	}
	
	public String getSplatsInstruction(String dest, String source) {
		String result = "      ";
		for(int i=0; i<vectorLength; i++) {
			result += dest + ".data[" + i + "] = " + source + ";\n      ";
		}
		return result + "\n";
	}

	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		String result = "      ";
		for(int i=0; i<vectorLength; i++) {
			result += dest + ".data[" + i + "] = (" + source1 + ".data[" + i + "] == " + source2 + ".data[" + i + "]) ? 1 : 0;\n      ";
		}
		return result + "\n";
	}
	
	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		String result = "      ";
		for(int i=0; i<vectorLength; i++) {
			result += dest + ".data[" + i + "] = (" + condition + ".data[" + i + "] == 1) ? " + resultOne + ".data[" + i + "]" + " : " + resultZero + ".data[" + i + "]" + ";\n      ";
		}
		return result + "\n";
	}

	public String getVectorUnsignedCharTypename() {
		return "vec_uchar";
	}

	public String getVectorUnsignedCharDefinition() {
		String result = "typedef struct vec_uchar_s {\n";
		result += "   uchar data[16];\n";
		result += "} vec_uchar;\n\n";
		return result;
	}

	public String getVectorBoolCharTypename() {
		return "vec_uchar";
	}
	
}
