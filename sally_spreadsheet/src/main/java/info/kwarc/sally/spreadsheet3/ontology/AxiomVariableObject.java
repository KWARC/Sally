package info.kwarc.sally.spreadsheet3.ontology;

/**
 * A class to represent a variable (e.g. for axioms).
 * The class contains informations about the type of the quantor (all, exist), the name and type.
 * @author cliguda
 *
 */
public class AxiomVariableObject {
	
	public enum QuantorType {All, Exist};
	
	QuantorType quantorType;
	String name, type;
	
	
	public AxiomVariableObject(QuantorType quantorType, String name, String type) {
		super();
		this.quantorType = quantorType;
		this.name = name;
		this.type = type;
	}
	
	public AxiomVariableObject(QuantorType quantorType, String name) {
		super();
		this.quantorType = quantorType;
		this.name = name;
		this.type = "";
	}
	
	public QuantorType getQuantorType() {
		return quantorType;
	}

	public String getName() {
		return name;
	}

	public String getType() {
		return type;
	}
	
	public void setType(String type) {
		this.type = type;
	}
	
	@Override
	public String toString() {
		return "Quantor: " + this.quantorType.name() + " Name: " + this.name + " Type: " + this.type; 
	}


	
}
