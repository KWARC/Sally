package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

public class DataSymbolInformation {
	
	String ontologyType;
	String content;
	CellSpaceInformation position;
	int symbolID;
	
	public DataSymbolInformation(String ontologyType, String content, CellSpaceInformation postition) {
		super();
		this.ontologyType = ontologyType;
		this.content = content;
		this.position = postition;
		this.symbolID = -1;
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
	
	@Override
	public String toString() {
		return "[ Position: " + position.toString() + " | ID: " + symbolID + " | Type: " + ontologyType + " | Content: " + content + " ]";
	}
	
}
