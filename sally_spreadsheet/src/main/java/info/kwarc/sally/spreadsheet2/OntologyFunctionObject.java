package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class OntologyFunctionObject {
	
	String uri;
	List<String> argumentTypes;
	List<String> variableNames;
	String resultType;
	String mathMLDefinition;
	String mathMLAxiom;
	
	public OntologyFunctionObject(String uri, List<String> argumentTypes,
			List<String> variableNames, String resultType,
			String mathMLDefinition, String mathMLAxiom) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		this.variableNames = variableNames;
		this.resultType = resultType;
		this.mathMLDefinition = mathMLDefinition;
		this.mathMLAxiom = mathMLAxiom;
	}
	
	public OntologyFunctionObject(String uri, List<String> argumentTypes, 
			String resultType, String mathMLAxiom) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		this.variableNames = new ArrayList<String>();
		this.resultType = resultType;
		this.mathMLDefinition = "";
		this.mathMLAxiom = mathMLAxiom;
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

	public String getMathMLAxiom() {
		return mathMLAxiom;
	}
	
}
