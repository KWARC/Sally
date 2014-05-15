package info.kwarc.sally.spreadsheet3.ontology;

/**
 * A class to provide the basic type for an ontology object.
 * @author cliguda
 *
 */
public class DataTypeObject {
	
	public enum BasicType {Int, Real, String, Bool};
	
	String uri;
	BasicType basicType;
	
	public DataTypeObject(String uri, BasicType basicType) {
		super();
		this.uri = uri;
		this.basicType = basicType;
	}

	public String getUri() {
		return uri;
	}

	public BasicType getBasicType() {
		return basicType;
	}
	
}
