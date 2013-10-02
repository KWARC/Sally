package info.kwarc.sally.spreadsheet3.ontology;

//import java.util.ArrayList;
import java.util.List;

public class FunctionObject {
	
	String uri;
	List<String> argumentTypes;
	//List<String> variableNames;
	String resultType;
	String mlDefinition;
	BuilderML builderML;
	
	public FunctionObject(String uri, List<String> argumentTypes, String resultType,
			String mlDefinition, BuilderML builderML) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		//this.variableNames = variableNames;
		this.resultType = resultType;
		this.mlDefinition = mlDefinition;
		this.builderML = builderML;
	}
	
	public FunctionObject(String uri, List<String> argumentTypes, 
			String resultType) {
		super();
		this.uri = uri;
		this.argumentTypes = argumentTypes;
		this.resultType = resultType;
		this.mlDefinition = "";
		this.builderML = null;
	}

	public String getUri() {
		return uri;
	}

	public List<String> getArgumentTypes() {
		return argumentTypes;
	}

	/*public List<String> getVariableNames() {
		return variableNames;
	}*/

	public String getResultType() {
		return resultType;
	}

	public String getMLDefinition() {
		return mlDefinition;
	}
	
	public BuilderML getBuilderML() {
		return builderML;
	}

}
