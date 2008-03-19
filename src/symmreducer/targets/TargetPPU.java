package src.symmreducer.targets;


public class TargetPPU extends Target {

	@Override
	public int alignmentValue() {
		return 16;
	}

	@Override
	public String getSplatsInstruction(String dest, String source) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getCompareEqualInstruction(String dest, String source1, String source2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getSelectInstruction(String dest, String condition, String resultOne, String resultZero) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getVectorUnsignedCharTypename() {
		return "vec_char";
	}

	@Override
	public String getVectorUnsignedCharDefinition() {
		// TODO Auto-generated method stub
		return null;
	}

}
