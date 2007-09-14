package src.etch.error;

public class IncompatibleTypesError extends Error {

    private String type1;
    private String type2;

    public IncompatibleTypesError(String t1, String t2) {
	type1 = t1;
	type2 = t2;
    }

    public String message() {
	return "\"" + type1 + "\" is not compatible with type \"" + type2 + "\" (mismatch found during type unification)";
	
    } 

}
