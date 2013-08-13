package info.kwarc.sally.spreadsheet2;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Manager {
	
	FormalSpreadsheet spreadsheet;
	Map<Integer, Block> blocks;
	Map<Integer, Relation> relations;
	int maxBlockID, maxRelationID;
	
	Map<CellSpaceInformation, List<Integer>> positionToBlockId;
	Map<CellSpaceInformation, List<Integer>> positionToRelationId;
	
	final Logger logger = LoggerFactory.getLogger(Manager.class);
	
	/**
	 * A Manager manages the abstract structure and ontology linking for one spreadsheet.
	 * @param spreadsheet 
	 */
	public Manager(FormalSpreadsheet spreadsheet) {
		this.spreadsheet = spreadsheet;
		this.blocks = new HashMap<Integer, Block>();
		this.relations = new HashMap<Integer, Relation>();
		this.maxBlockID = 0;
		this.maxRelationID = 0;
		
		positionToBlockId = new HashMap<CellSpaceInformation, List<Integer>>();
		positionToRelationId = new HashMap<CellSpaceInformation, List<Integer>>();
	}

	
	// ---------- Methods for the Spreadsheet Annotation Model ----------

	public int createAtomicBlock(CellSpaceInformation position) {
		maxBlockID++;
		blocks.put(maxBlockID, new BlockAtomic(maxBlockID, position));
		addPositionToBlockLink(position, maxBlockID);
		return maxBlockID;
	}
	
	public int createBlock(List<Block> blocks) {
		maxBlockID++;
		this.blocks.put(maxBlockID, new BlockComposed(maxBlockID, blocks));
		for (Block block : blocks )
			addPositionsToBlockLink(block.getCells(), maxBlockID);
		return maxBlockID;
	}
	
	public int createComposedBlock(List<CellSpaceInformation> positions) {
		List<Block> blocks = new ArrayList<Block>();
		for (CellSpaceInformation pos : positions)
			blocks.add(getBlockByID(createAtomicBlock(pos)));
		return createBlock(blocks);
	}
	
	public int createFunctionalRelation(List<Block> blocks, String function) {
		List<CellTuple> cellRelations = createFunctionalCellRelations(blocks);
		maxRelationID++;
		this.relations.put(maxRelationID, new RelationFunctional(maxRelationID, blocks, function, cellRelations));
		for (Block block : blocks )
			addPositionsToRelationLink(block.getCells(), maxRelationID);
		return maxRelationID;
	}
	
	public Block getBlockByID(int id) {
		return blocks.get(id);
	}
	
	public Relation getRelationByID(int id) {
		return relations.get(id);
	}
	
	public List<Integer> getBlocksForPosition(CellSpaceInformation position) {
		return new ArrayList<Integer>(positionToBlockId.get(position));
	}
	
	public List<Integer> getRelationForPosition(CellSpaceInformation position) {
		return new ArrayList<Integer>(positionToRelationId.get(position));
	}
	
	public List<CellTuple> getCellRelationsForPosition(CellSpaceInformation position) {
		List<CellTuple> cellRelations = new ArrayList<CellTuple>();
		for (Integer relationId : getRelationForPosition(position)) {
			Relation r = getRelationByID(relationId);
			if (r instanceof RelationFunctional) {
				RelationFunctional relFunc = (RelationFunctional) r;
				cellRelations.addAll(relFunc.getCellRelationFor(position));
			}
		}
		return cellRelations;
	}
	
	private void addPositionToBlockLink(CellSpaceInformation position, int id) {
		if (positionToBlockId.containsKey(position)) {
			positionToBlockId.get(position).add(id);
		} else {
			List<Integer> idList = new ArrayList<Integer>();
			idList.add(id);
			positionToBlockId.put(position, idList);
		}
	}
	
	private void addPositionsToBlockLink(List<CellSpaceInformation> positions, int id) {
		for (CellSpaceInformation position : positions)
			addPositionToBlockLink(position, id);
	}
	
	private void addPositionToRelationLink(CellSpaceInformation position, int id) {
		if (positionToRelationId.containsKey(position)) {
			positionToRelationId.get(position).add(id);
		} else {
			List<Integer> idList = new ArrayList<Integer>();
			idList.add(id);
			positionToRelationId.put(position, idList);
		}
	}
	
	private void addPositionsToRelationLink(List<CellSpaceInformation> positions, int id) {
		for (CellSpaceInformation position : positions)
			addPositionToRelationLink(position, id);
	}
	
	private List<CellTuple> createFunctionalCellRelations(List<Block> blocks) {
		List<CellTuple> cellRelations = new ArrayList<CellTuple>();
		
		Block codomain = blocks.get(blocks.size()-1);
		blocks.remove(blocks.size()-1);
		
		for (CellSpaceInformation pos : codomain.getCells())
			cellRelations.add(getAssociatedCells(blocks, pos));
		
		return cellRelations;
	}
	
	private CellTuple getAssociatedCells(List<Block> blocks, CellSpaceInformation position) {
		List<CellSpaceInformation> assocPositions = new ArrayList<CellSpaceInformation>();  
		
		for (Block b : blocks) {
			List<CellSpaceInformation> assocBlockPositions = new ArrayList<CellSpaceInformation>();
			for (CellSpaceInformation blockPos : b.getCells()) {
				if (position.isAssociated(blockPos))
					assocBlockPositions.add(blockPos);
			}
			if (assocBlockPositions.size() == 0) {
				 logger.info(String.format("Position %s does not have a corresponding label entry.", position));
				 assocPositions.add(null);
			} else if (assocBlockPositions.size() > 1) {
				 logger.info(String.format("Positions %s depends on multiple elements of one label.", position));
				 assocPositions.add(null);
			} else
				 assocPositions.add(assocBlockPositions.get(0));
		}
		assocPositions.add(position);
		
		return new CellTuple(assocPositions);
	}

}
