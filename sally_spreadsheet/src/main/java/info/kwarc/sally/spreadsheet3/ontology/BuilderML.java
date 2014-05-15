package info.kwarc.sally.spreadsheet3.ontology;

/**
 * BuilderML is an abstract builder for XML expressions in e.g. MathML or OpenMath.
 * By using BuilderML no MathML or OpenMath expressions are necessary in the project code.
 * @author cliguda
 *
 */
public abstract class BuilderML {
	
	public abstract String getVIVaribale(int i);
	
	public abstract String getIdentifier(String s);
	
	public abstract String getMathTagBegin();
	
	public abstract String getMathTagEnd();
	
	public abstract String getOperatorApplication(String cd, String symbol);
	
	public abstract String getApplicationEnd();
	
	public abstract AxiomObject parseMLAxiom(String uri, String axiom) throws OntologyException;

}
