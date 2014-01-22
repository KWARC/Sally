package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

public class DataSymbolInformation {
	
	String ontologyType;
	String content;
	CellSpaceInformation position;
	int symbolID;
	String z3String;
	
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
