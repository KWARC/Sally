package info.kwarc.sally.spreadsheet3.ontology;

import java.util.List;


public class AxiomObject {
	
	String uri;
	List<AxiomVariableObject> variables;
	String varConditions;
	String constrain;
	
	public AxiomObject(String uri, List<AxiomVariableObject> variables, String varConditions,
			String mlConstrain) {
		super();
		this.uri = uri;
		this.variables = variables;
		this.varConditions = varConditions;
		this.constrain = mlConstrain;
	}

	public String getUri() {
		return uri;
	}
	
	public List<AxiomVariableObject> getVariables() {
		return variables;
	}
	
	public String getVarConditions() {
		return varConditions;
	}

	public String getMLConstrain() {
		return constrain;
	}
	
	@Override
	public String toString() {
		String result = "Variables:\n";
		for (AxiomVariableObject var : variables)
			result = result + var.toString() + "\n";
		result = result + "Conditions:\n" + varConditions;
		result = result + "Axiom:\n" + constrain;
		return result;
	}
	
}
