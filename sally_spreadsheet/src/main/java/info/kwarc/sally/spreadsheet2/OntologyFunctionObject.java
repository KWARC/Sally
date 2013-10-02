package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class OntologyFunctionObject {
	
	String uri;
	List<String> argumentTypes;
	List<String> variableNames;
	String resultType;
	String mathMLDefinition;
	
	public OntologyFunctionObject(String uri, List<String> argumentTypes,
			List<String> variableNames, String resultType,
			String mathMLDefinition) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		this.variableNames = variableNames;
		this.resultType = resultType;
		this.mathMLDefinition = mathMLDefinition;
	}
	
	public OntologyFunctionObject(String uri, List<String> argumentTypes, 
			String resultType) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		this.variableNames = new ArrayList<String>();
		this.resultType = resultType;
		this.mathMLDefinition = "";
	}

	public String getUri() {
		return uri;
	}

	public List<String> getArgumentTypes() {
		return argumentTypes;
	}

	public List<String> getVariableNames() {
		return variableNames;
	}

	public String getResultType() {
		return resultType;
	}

	public String getMathMLDefinition() {
		return mathMLDefinition;
	}

	
}
