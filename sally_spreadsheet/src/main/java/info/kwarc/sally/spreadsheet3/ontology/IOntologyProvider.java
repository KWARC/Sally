package info.kwarc.sally.spreadsheet3.ontology;

import java.util.List;
import java.util.Map;


/**
 * As long as we do not have a working ontology framework, we access a faked ontology by providing this interface. 
 * This interface allows to map URIs to function objects that contain a detailed specification of the ontology function. 
 * @author cliguda
 *
 */
public abstract class IOntologyProvider {

	BuilderML builderML;
	
	public IOntologyProvider(BuilderML builderML) {
		this.builderML = builderML;
	}
	
	public BuilderML getBuilderML() {
		return this.builderML;
	}

	abstract public FunctionObject getFunctionObject(String uri);
	
	abstract public List<FunctionObject> getAllBasicFunctionObjects();
	
	abstract public Map<String, FunctionObject> getBasicFunctionObjectMap();
	
	abstract public List<FunctionObject> getAllDomainFunctionObjects();
	
	abstract public Map<String, FunctionObject> getDomainFunctionObjectMap();
	
	abstract public DataTypeObject getDataTypeObject(String uri);
	
	abstract public List<DataTypeObject> getAllDataTypeObjects();
	
	abstract public Map<String, DataTypeObject> getDataTypeObjectMap();
	
	abstract public List<AxiomObject> getAxioms() throws OntologyException;

}
