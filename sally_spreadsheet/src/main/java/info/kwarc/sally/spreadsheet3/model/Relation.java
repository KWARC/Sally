package info.kwarc.sally.spreadsheet3.model;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Relation {
	
	public enum RelationType {
		FUNCTIONALRELATION, TYPERELATION
	}
	
	int id;
	RelationType relationType;
	String uri;
	List<Block> blocks;
	List<CellTuple> cellRelations;
	List<CellDependencyDescription> cellDependencyDescriptions;
	
	final Logger logger = LoggerFactory.getLogger(Relation.class);
	
	public Relation(int id, RelationType relationType, List<Block> blocks,
			List<CellTuple> cellRelations, List<CellDependencyDescription> cellDependencyDescriptions, String uri) {
		super();
		if (isConsistent(blocks, cellRelations)) {
			this.id = id;
			this.relationType = relationType;
			this.uri = uri;
			this.blocks = new ArrayList<Block>(blocks);
			this.cellRelations = new ArrayList<CellTuple>(cellRelations);
			this.cellDependencyDescriptions = new ArrayList<CellDependencyDescription>(cellDependencyDescriptions);
		} else 
			throw new java.lang.IllegalArgumentException("Cell realations is not consistent to blocks.");
	}
	
	public Relation(int id, RelationType relationType, List<Block> blocks,
			List<CellTuple> cellRelations, List<CellDependencyDescription> cellDependencyDescriptions) {
		this(id, relationType, blocks, cellRelations, cellDependencyDescriptions, "");
	}
	
	public Relation(sally.RelationMsg msg, Manager manager) {
		super();
		List<Block> msgBlocks = new ArrayList<Block>();
		for (Integer id : msg.getBlockIDsList())
			msgBlocks.add(manager.getBlockByID(id));
		List<CellTuple> msgCellRelations = new ArrayList<CellTuple>();
		for (sally.CellTupleMsg cellTupleMsg : msg.getCellRelationsList())
			msgCellRelations.add(new CellTuple(cellTupleMsg));
		if (isConsistent(msgBlocks, msgCellRelations)) {
			this.id = msg.getId();
			this.relationType = RelationType.values()[msg.getRelationType()];
			this.uri = msg.getUri();
			this.blocks = msgBlocks;
			this.cellRelations = msgCellRelations;
			this.cellDependencyDescriptions = new ArrayList<CellDependencyDescription>();
			for (sally.CellDependencyDescriptionMsg msgCDD: msg.getCellDependencyDescriptionsList())
				cellDependencyDescriptions.add(new CellDependencyDescription(msgCDD));
		} else {
			logger.error("Inconsistent cell relations:");
			for (CellTuple ct : cellRelations) 
				logger.error(ct.toString());
			
			throw new java.lang.IllegalArgumentException("Cell realations is not consistent to blocks.");
		}
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
		result = prime
				* result
				+ ((cellDependencyDescriptions == null) ? 0
						: cellDependencyDescriptions.hashCode());
		result = prime * result
				+ ((cellRelations == null) ? 0 : cellRelations.hashCode());
		result = prime * result + id;
		result = prime * result
				+ ((relationType == null) ? 0 : relationType.hashCode());
		result = prime * result + ((uri == null) ? 0 : uri.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Relation other = (Relation) obj;
		if (blocks == null) {
			if (other.blocks != null)
				return false;
		} else if (!blocks.equals(other.blocks))
			return false;
		if (cellDependencyDescriptions == null) {
			if (other.cellDependencyDescriptions != null)
				return false;
		} else if (!cellDependencyDescriptions
				.equals(other.cellDependencyDescriptions))
			return false;
		if (cellRelations == null) {
			if (other.cellRelations != null)
				return false;
		} else if (!cellRelations.equals(other.cellRelations))
			return false;
		if (id != other.id)
			return false;
		if (relationType == null) {
			if (other.relationType != null)
				return false;
		} else if (!relationType.equals(other.relationType))
			return false;
		if (uri == null) {
			if (other.uri != null)
				return false;
		} else if (!uri.equals(other.uri))
			return false;
		return true;
	}

	public int getId() {
		return this.id;
	}
	
	public RelationType getRelationType() {
		return this.relationType;
	}
	
	public String getUri() {
		return this.uri;
	}
	
	public void setUri(String uri) {
		this.uri = uri;
	}
	
	public List<Block> getBlocks() {
		return new ArrayList<Block>(this.blocks);
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
	
	public sally.RelationMsg serialize() {
		sally.RelationMsg.Builder msg = sally.RelationMsg.newBuilder();
		msg.setId(this.id);
		msg.setRelationType(this.relationType.ordinal());
		msg.setUri(this.uri);
		for (Block b : blocks)
			msg.addBlockIDs(b.getId());
		for (CellTuple cellTuple : cellRelations)
			msg.addCellRelations(cellTuple.serialize());
		for (CellDependencyDescription cellDependencyDescription : this.cellDependencyDescriptions)
			msg.addCellDependencyDescriptions(cellDependencyDescription.serialize());
		
		return msg.build();
	}

}
