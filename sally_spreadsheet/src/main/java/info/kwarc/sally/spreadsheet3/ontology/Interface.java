package info.kwarc.sally.spreadsheet3.ontology;


/**
 * As long as we do not have a working ontology framework, we access a faked ontology by providing this interface. 
 * This interface allows to map URIs to function objects that contain a detailed specification of the ontology function. 
 * @author cliguda
 *
 */
public abstract class Interface {

	BuilderML builderML;
	
	public Interface(BuilderML builderML) {
		this.builderML = builderML;
	}
	
	public BuilderML getBuilderML() {
		return this.builderML;
	}

	abstract public FunctionObject getFunctionObject(String uri);

}
