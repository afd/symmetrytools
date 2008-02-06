package src.utilities;

public class ProgressPrinter {

	public static boolean QUIET_MODE = false;
	
	public static void println(String line) {
		if(!QUIET_MODE) {
			System.out.println(line);
		}
	}

	public static void printSeparator() {
		if(!QUIET_MODE) {
			System.out.println("--------------------------------------");
		}
	}

	public static void print(String string) {
		if(!QUIET_MODE) {
			System.out.print(string);
		}
	}
}
