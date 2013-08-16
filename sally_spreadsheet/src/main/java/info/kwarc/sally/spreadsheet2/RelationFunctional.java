package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

class RelationFunctional extends Relation {
	String function;
	List<CellTuple> cellRelations;
	
	final Logger logger = LoggerFactory.getLogger(RelationFunctional.class);
		
	public RelationFunctional(int id, List<Block> blocks, String function, List<CellTuple> cellRelations) {
		super(id, blocks);
		if (isConsistent(blocks, cellRelations)) {
			this.function = function;
			this.cellRelations = cellRelations;
		} else 
			throw new java.lang.IllegalArgumentException("Cell realations is not consistent to blocks.");
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((cellRelations == null) ? 0 : cellRelations.hashCode());
		result = prime * result
				+ ((function == null) ? 0 : function.hashCode());
		return result;
	}


	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		RelationFunctional other = (RelationFunctional) obj;
		if (cellRelations == null) {
			if (other.cellRelations != null)
				return false;
		} else if (!cellRelations.equals(other.cellRelations))
			return false;
		if (function == null) {
			if (other.function != null)
				return false;
		} else if (!function.equals(other.function))
			return false;
		return true;
	}

	public String getFunction() {
		return function;
	}

	public void setFunction(String function) {
		this.function = function;
	}

	public List<CellTuple> getCellRelations() {
		return new ArrayList<CellTuple>(cellRelations);
	}
	
	public List<CellTuple> getCellRelationFor(CellSpaceInformation position) {
		List<CellTuple> tuples = new ArrayList<CellTuple>();
		for (CellTuple relation : cellRelations) {
			if (relation.contains(position))
				tuples.add(relation);
		}
		return tuples;
	}

	public void setCellRelations(List<CellTuple> cellRelations) {
		this.cellRelations = cellRelations;
	}
	
	private Boolean isConsistent(List<Block> blocks, List<CellTuple> cellRelations) {

		boolean consistent = true;
		for (CellTuple tuple : cellRelations) {
			if (tuple.getSize() != blocks.size()) {
				consistent = false;
			} else {
				for (int i = 0; i < tuple.getSize(); i++) {
					if (!blocks.get(i).getCells().contains(tuple.getTuple().get(i))) {
						consistent = false;
					}
				}
			}
			
		}
		return consistent;
	}
	
}
