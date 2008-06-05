package src.symmreducer.targets;

public abstract class Target {

	private static Target targetArchitecture;

	public static Target getTargetArchitecture() {
		return targetArchitecture;
	}

	public static void setTargetArchitecture(Target t) {
		targetArchitecture = t;
	}

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
