package src.utilities;


public class ConfigurationOptionEntry<T> {

	private T defaultValue;
	private T userSetValue;
	private String description;
	
	ConfigurationOptionEntry(T defaultValue, String description) {
		this.defaultValue = defaultValue;
		userSetValue = null;
		this.description = description;
	}

	void setValue(T value) {
		this.userSetValue = value;
	}
	
	void setToDefaultValue() {
		this.userSetValue = defaultValue;
	}
	
	public T getValue() {
		return userSetValue;
	}
	
	public String getDescription() {
		return description;
	}

	public String helpString(String optionName, String type) {
		return "\nOption         : " + optionName.toLowerCase() + "\n" +
			   "Description    : " + description + "\n" +
		       "Expected value : " + type + "\n" +
		       "Default value  : " + (null==defaultValue ? "not set by default" : defaultValue.toString()) + "\n";
	}

}
