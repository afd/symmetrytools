package src.utilities;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

public class CommunicatingProcess {

	public static Process create(String command) throws IOException {
		return Runtime.getRuntime().exec(command);
	}
	
	public static BufferedWriter getWriter(Process gap) {
		return new BufferedWriter(new OutputStreamWriter(gap
				.getOutputStream()));
	}

	public static BufferedReader getReader(Process gap) {
		return new BufferedReader(new InputStreamReader(gap
				.getInputStream()));
	}

	public static BufferedReader getError(Process p) {
		return new BufferedReader(new InputStreamReader(p.getErrorStream()));
	}
	
	public static void execute(String command, String option, String argument)
	throws IOException, InterruptedException {

		Process p = create(command + " " + option + " " + argument);

		try {
			p.waitFor();
		} catch (InterruptedException e) {
			System.out.println("Error executing command \"" + command + " "
					+ option + " " + argument + "\".");
			throw e;
		}
	}
	
	
}
