package src.exceptions;

import java.util.List;

@SuppressWarnings("serial")
public class IllegalLocalAssignmentException extends Exception {

	List<Integer> illegalAssignment;
	
	public IllegalLocalAssignmentException(List<Integer> illegalAssignment) {
		this.illegalAssignment = illegalAssignment;
	}

	public String toString() {
		return "Attempt to compute abstract value of illegal assignment " + illegalAssignment;
	}
}
