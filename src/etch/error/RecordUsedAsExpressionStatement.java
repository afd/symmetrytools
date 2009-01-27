package src.etch.error;

public class RecordUsedAsExpressionStatement extends Error {

	private String recordTypeName;
	
	public RecordUsedAsExpressionStatement(String recordTypeName) {
		this.recordTypeName = recordTypeName;
	}

	@Override
	public String message() {
		return "Instance of record type \"" + recordTypeName + "\" cannot be used as an expression statement";
	}

}
