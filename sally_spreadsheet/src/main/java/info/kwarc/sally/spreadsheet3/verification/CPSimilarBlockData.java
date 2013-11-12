package info.kwarc.sally.spreadsheet3.verification;

import java.util.Map;

import info.kwarc.sally.spreadsheet3.model.Relation;

public class CPSimilarBlockData {
	
	Relation relation;
	String antiunification;
	Map<Integer, String> constantArguments;
	
	public CPSimilarBlockData(Relation relation, String antiunification,
			Map<Integer, String> constantArguments) {
		super();
		this.relation = relation;
		this.antiunification = antiunification;
		this.constantArguments = constantArguments;
	}

	public Relation getRelation() {
		return relation;
	}

	public String getAntiunification() {
		return antiunification;
	}

	public Map<Integer, String> getConstantArguments() {
		return constantArguments;
	}
	
	

}
