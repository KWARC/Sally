package info.kwarc.sally.spreadsheet3.verification;

import java.util.List;
import java.util.Map;

public class DataTypeSpec {
	
	List<String> specification;
	Map<String, String> identifierToSymbol;
	
	public DataTypeSpec(List<String> specification,
			Map<String, String> identifierToSymbol) {
		super();
		this.specification = specification;
		this.identifierToSymbol = identifierToSymbol;
	}

	public List<String> getSpecification() {
		return specification;
	}

	public Map<String, String> getIdentifierToSymbol() {
		return identifierToSymbol;
	}
	

}
