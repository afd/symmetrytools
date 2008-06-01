package src.testing;



public abstract class TestCase {

	protected String filename;

	private TestOutcome expectedOutcome;
	protected TestOutcome actualOutcome;
	
	public TestCase(String filename, TestOutcome outcome) {
		this.filename = filename;
		this.expectedOutcome = outcome;
	}

	public boolean isPass() {
		return expectedOutcome.matches(actualOutcome);
	}

	public abstract void run();

	public void displayResult() {
		System.out.print("   ");
		if(isPass()) {
			System.out.println("[PASS] expected and actual: " + expectedOutcome + ", file: " + filename);
		} else {
			System.out.println("[FAIL] expected: " + expectedOutcome + ", actual: " + actualOutcome + ", file: " + filename);
		}
	}

}
