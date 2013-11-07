package info.kwarc.sally.spreadsheet3.verification;

import java.util.List;
import java.util.Map;

public class DataTypeSpec {
	
	List<String> specification;
	Map<String, String> viToZ3String;			// Maps a value interpretation for a string to a Z3 Identifier (e.g. <ci>Total Costs</ci> -> Total_Costs)
	
	public DataTypeSpec(List<String> specification,
			Map<String, String> viToZ3String) {
		super();
		this.specification = specification;
		this.viToZ3String = viToZ3String;
	}

	public List<String> getSpecification() {
		return specification;
	}

	public Map<String, String> getViToZ3StringMap() {
		return viToZ3String;
	}
	

}
