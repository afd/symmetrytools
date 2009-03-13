package src.testing;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.StringTokenizer;

import src.GRIP;
import src.symmetricprism.lexer.LexerException;
import src.symmetricprism.parser.ParserException;
import src.translator.ModelType;
import src.utilities.Config;

public class GRIPTestCase extends TestCase {

	private static final String reducedSpecification = "reduced_test";

	private boolean optimise;
	
	private boolean eliminate;
	
	public GRIPTestCase(String filename, boolean optimise, boolean eliminate, TestOutcome outcome) {
		super(filename, outcome);
		this.optimise = optimise;
		this.eliminate = eliminate;
	}

	public GRIPTestCase(String filename, TestOutcome outcome) {
		this(filename, false, false, outcome);
	}
	
	@Override
	public void run() {
		
		try {
			GRIP.translateSpecification(optimise, eliminate, filename, reducedSpecification, null, null);
			
			actualOutcome = runPRISMOnReducedSpecification();
			
		} catch (FileNotFoundException e) {
			actualOutcome = SystemErrorTestOutcome.FileNotFound;
		} catch (ParserException e) {
			actualOutcome = GRIPFailTestOutcome.ParserError;
		} catch (LexerException e) {
			actualOutcome = GRIPFailTestOutcome.LexerError;
		} catch (IOException e) {
			actualOutcome = SystemErrorTestOutcome.IOError;
		}

	}

	
	private TestOutcome runPRISMOnReducedSpecification() {

		Process prism;
		try {
			if(Config.isOSWindows()) {
				prism = Runtime.getRuntime().exec("prism.bat -noprobchecks -fixdl " + reducedSpecification);
			} else {
				prism = Runtime.getRuntime().exec("prism -noprobchecks -fixdl " + reducedSpecification);
			}
		} catch (IOException e) {
			return GRIPFailTestOutcome.PRISMIOError;
		}

		BufferedReader br = new BufferedReader(new InputStreamReader(prism.getInputStream()));

		ModelType modelType = null;
		long numberOfNodes = -1;
		long numberOfStates = -1;
		long numberOfTransitions = -1;
		long numberOfChoices = -1;
		
		String line;

		try
		{
			while((line = br.readLine())!=null) {
				if(line.contains("Transition matrix:") || line.contains("Rate matrix:")) {
					numberOfNodes = getFirstNumberFromLine(line);
				} else if(line.contains("States:")) {
					numberOfStates = getFirstNumberFromLine(line);
				} else if(line.contains("Transitions:")) {
					numberOfTransitions = getFirstNumberFromLine(line);
				} else if(line.contains("Choices:")) {
					numberOfChoices = getFirstNumberFromLine(line);
				} else if(line.contains("Type:")) {
					modelType = getModelTypeFromLine(line);
				}
			}
		} catch(NumberFormatException e) {
			prism.destroy();
			return GRIPFailTestOutcome.ErrorParsingVerificationResult;
		} catch (IOException e) {
			System.out.println(e);
			return GRIPFailTestOutcome.PRISMIOError;
		}

		try {
			prism.waitFor();
		} catch (InterruptedException e) {
			return GRIPFailTestOutcome.PRISMInterrupted;
		}

		if(0 != prism.exitValue()) {
			return GRIPFailTestOutcome.PRISMError;
		}

		return new GRIPPassTestOutcome(modelType, numberOfNodes, numberOfStates, numberOfTransitions, numberOfChoices);
		
	}

	private ModelType getModelTypeFromLine(String line) {

		StringTokenizer strtok = new StringTokenizer(line, " ");
		strtok.nextToken();
		String typeString = strtok.nextToken();
		
		if(typeString.equals("Stochastic")) {
			return ModelType.stochastic;
		}
		
		if(typeString.equals("Nondeterministic")) {
			return ModelType.nondeterministic;
		}
		
		assert(typeString.equals("Probabilistic"));
		
		return ModelType.probabilistic;

	}

	private long getFirstNumberFromLine(String line) {
		int indexOfStartOfNumber = 0;
		while(! Character.isDigit(line.charAt(indexOfStartOfNumber))) {
			indexOfStartOfNumber++;
		}
		return Long.parseLong( new StringTokenizer(line.substring(indexOfStartOfNumber)," ").nextToken());
	}
	
}
