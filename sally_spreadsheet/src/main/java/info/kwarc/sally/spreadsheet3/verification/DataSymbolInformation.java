package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

/**
 * This class represents a symbol for an instance of an ontology object, e.g. a concrete year for the ontology object "year".
 * Symbols are needed for verification tasks to abstract over cell positions.
 * @author cliguda
 *
 */
public class DataSymbolInformation {
	
	String ontologyType;
	String content;
	CellSpaceInformation position;
	int symbolID;
	String z3String;
	
	/**
	 * Creates a symbol for an ontology object.
	 * @param ontologyType The uri of the ontology object.
	 * @param content The content (value interpretation) of a cell.
	 * @param position The cell position. 
	 * @param symbolID Each symbol needs an unique id.
	 */
	public DataSymbolInformation(String ontologyType, String content, CellSpaceInformation postition, int symbolID) {
		super();
		this.ontologyType = ontologyType;
		this.content = content;
		this.position = postition;
		this.symbolID = symbolID;
		this.z3String = "";
	}

	public String getOntologyType() {
		return ontologyType;
	}

	public String getContent() {
		return content;
	}

	public CellSpaceInformation getPostition() {
		return position;
	}
	
	public void setSymbolID(int symbolID) {
		this.symbolID = symbolID;
	}
	
	public int getSymbolID() {
		return symbolID;
	}
	/*
	public void setZ3String(String z3String) {
		this.z3String = z3String;
	}
	
	public String getZ3String() {
		//return content.trim().replaceAll(" ", "-");
		return z3String;
	}*/
	
	@Override
	public String toString() {
		return "[ Position: " + position.toString() + " | ID: " + symbolID + " | Type: " + ontologyType + " | Content: " + content + " ]";
	}
	
}
