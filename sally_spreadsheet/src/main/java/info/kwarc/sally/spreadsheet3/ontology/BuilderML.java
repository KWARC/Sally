package info.kwarc.sally.spreadsheet3.ontology;


public abstract class BuilderML {
	
	public abstract String getVIVaribale(int i);
	
	public abstract String getIdentifier(String s);
	
	public abstract String getMathTagBegin();
	
	public abstract String getMathTagEnd();
	
	public abstract String getOperatorApplication(String cd, String symbol);
	
	public abstract String getApplicationEnd();
	
	public abstract AxiomObject parseMLAxiom(String axiom);

}
