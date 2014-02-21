package info.kwarc.sally.spreadsheet3.verification;

import java.util.Map;

import info.kwarc.sally.spreadsheet3.model.Relation;

/**
 * This class represents the data of a cp-similar block.
 * A block is called cp-similar, if it is not atomic and all formulae are equal except cell references.
 * @author cliguda
 *
 */
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

	
	/**
	 * The ontology function for a block may have constant arguments on that block.
	 * In example a function ExpensesPerYear: CostType x Year -> Money may have the constant argument "TotalCosts" for a block. 
	 * @return
	 */
	public Map<Integer, String> getConstantArguments() {
		return constantArguments;
	}
	
	

}
