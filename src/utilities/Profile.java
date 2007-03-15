package src.utilities;

public class Profile {

	public static long PARSE_START = 0;
	public static long PARSE_END = 0;

	public static long EXTRACT_START = 0;
	public static long EXTRACT_END = 0;

	public static long GAP_LAUNCH_START = 0;
	public static long GAP_LAUNCH_END = 0;

	public static long SAUCY_START = 0;
	public static long SAUCY_END = 0;

	public static long LARGEST_VALID_START = 0;
	public static long LARGEST_VALID_END = 0;

	public static long CLASSIFY_START;
	public static long CLASSIFY_END;

	public static long CODE_GENERATION_START;
	public static long CODE_GENERATION_END;

	public static long TOPSPIN_START = 0;
	public static long TOPSPIN_END = 0;

	public static void show() {
		System.out.println("\nPROFILING INFORMATION");
		System.out.println("=====================");
		System.out.println("   Total: " + (TOPSPIN_END-TOPSPIN_START));
		if(PARSE_END != 0) {
			System.out.println("   Parsing: " + (PARSE_END-PARSE_START));
		}
		if(EXTRACT_END != 0) {
			System.out.println("   SCD Extraction: " + (EXTRACT_END-EXTRACT_START));
		}
		if(GAP_LAUNCH_END != 0) {
			System.out.println("   GAP Launch: " + (GAP_LAUNCH_END-GAP_LAUNCH_START));
		}
		if(SAUCY_END !=0) {
			System.out.println("   Saucy (including communication overhead): " + (SAUCY_END - SAUCY_START));
		}
		if(LARGEST_VALID_END !=0) {
			System.out.println("   Largest valid subgroup computation: " + (LARGEST_VALID_END - LARGEST_VALID_START));
		}
		if(CLASSIFY_END!=0) {
			System.out.println("   Group Classification: " + (CLASSIFY_END - CLASSIFY_START));
		}
		if(CODE_GENERATION_END!=0) {
			System.out.println("   Code generation: " + (CODE_GENERATION_END - CODE_GENERATION_START));
		}
		System.out.println("   House-keeping: " + ((TOPSPIN_END-TOPSPIN_START)-
				((PARSE_END-PARSE_START)+(EXTRACT_END-EXTRACT_START)+(GAP_LAUNCH_END-GAP_LAUNCH_START)
						+(SAUCY_END-SAUCY_START)+(LARGEST_VALID_END-LARGEST_VALID_START)+
						(CLASSIFY_END-CLASSIFY_START)+(CODE_GENERATION_END-CODE_GENERATION_START))));
	}
	
}
