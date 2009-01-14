package src.utilities;

public class ProgressPrinter {

	public static void println(String line) {
		if(!Config.inQuietMode()) {
			System.out.println(line);
		}
	}

	public static void printSeparator() {
		if(!Config.inQuietMode()) {
			System.out.println("--------------------------------------");
		}
	}

	public static void print(String string) {
		if(!Config.inQuietMode()) {
			System.out.print(string);
		}
	}

}
