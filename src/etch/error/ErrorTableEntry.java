package src.etch.error;


class ErrorTableEntry extends FeedbackTableEntry {

	public ErrorTableEntry(int line, Feedback feedback) {
		super(line,feedback);
	}

	protected final String kindOfFeedback() {
		return "Error";
	}

}
