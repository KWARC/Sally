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
	
	Map<CellSpaceInformation, Block> positionToAtomicBlock;
	Map<CellSpaceInformation, List<Block>> positionToBlocks;
	Map<CellSpaceInformation, List<Relation>> positionToRelations;
	
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
		
		positionToAtomicBlock = new HashMap<CellSpaceInformation, Block>();
		positionToBlocks = new HashMap<CellSpaceInformation, List<Block>>();
		positionToRelations = new HashMap<CellSpaceInformation, List<Relation>>();
	}

	
	// ---------- Methods for the Spreadsheet Annotation Model ----------

	public Block getOrCreateAtomicBlock(CellSpaceInformation position) {
		if (positionToAtomicBlock.containsKey(position))
			return positionToAtomicBlock.get(position);
		else {
			maxBlockID++;
			Block b = new BlockAtomic(maxBlockID, position);
			blocks.put(maxBlockID, b);
			addPositionToBlockLink(position, b);
			return b;
		}
	}
	
	public Block createBlock(List<Block> subBlocks) {
		maxBlockID++;
		Block b = new BlockComposed(maxBlockID, subBlocks);
		blocks.put(maxBlockID, b);
	    addPositionsToBlockLink(b.getCells(), b);
		return b;
	}
	
	public Block createComposedBlock(List<CellSpaceInformation> positions) {
		List<Block> blocks = new ArrayList<Block>();
		for (CellSpaceInformation pos : positions)
			blocks.add(getOrCreateAtomicBlock(pos));
		return createBlock(blocks);
	}
	
	public Relation createFunctionalRelation(List<Block> blocks, String function) {
		maxRelationID++;
		List<CellTuple> cellRelations = createFunctionalCellRelations(blocks);
		Relation r = new RelationFunctional(maxRelationID, blocks, function, cellRelations);
		this.relations.put(maxRelationID, r);
		for (Block block : blocks )
			addPositionsToRelationLink(block.getCells(), r);
		return r;
	}
	
	public Block getBlockByID(int id) {
		return blocks.get(id);
	}
	
	public Relation getRelationByID(int id) {
		return relations.get(id);
	}
	
	public List<Block> getBlocksForPosition(CellSpaceInformation position) {
		return new ArrayList<Block>(positionToBlocks.get(position));
	}
	
	public List<Relation> getRelationForPosition(CellSpaceInformation position) {
		return new ArrayList<Relation>(positionToRelations.get(position));
	}
	
	public List<CellTuple> getCellRelationsForPosition(CellSpaceInformation position) {
		List<CellTuple> cellRelations = new ArrayList<CellTuple>();
		for (Relation r : getRelationForPosition(position)) {
			if (r instanceof RelationFunctional) {
				RelationFunctional relFunc = (RelationFunctional) r;
				cellRelations.addAll(relFunc.getCellRelationFor(position));
			}
		}
		return cellRelations;
	}
	
	private void addPositionToBlockLink(CellSpaceInformation position, Block block) {
		if (positionToBlocks.containsKey(position)) {
			positionToBlocks.get(position).add(block);
		} else {
			List<Block> blockList = new ArrayList<Block>();
			blockList.add(block);
			positionToBlocks.put(position, blockList);
		}
	}
	
	private void addPositionsToBlockLink(List<CellSpaceInformation> positions, Block block) {
		for (CellSpaceInformation position : positions)
			addPositionToBlockLink(position, block);
	}
	
	private void addPositionToRelationLink(CellSpaceInformation position, Relation relation) {
		if (positionToRelations.containsKey(position)) {
			positionToRelations.get(position).add(relation);
		} else {
			List<Relation> relList = new ArrayList<Relation>();
			relList.add(relation);
			positionToRelations.put(position, relList);
		}
	}
	
	private void addPositionsToRelationLink(List<CellSpaceInformation> positions, Relation rel) {
		for (CellSpaceInformation position : positions)
			addPositionToRelationLink(position, rel);
	}
	
	private List<CellTuple> createFunctionalCellRelations(List<Block> blocks) {
		List<CellTuple> cellRelations = new ArrayList<CellTuple>();
		List<Block> allBlocks = new ArrayList<Block>(blocks);
		
		Block codomain = allBlocks.get(blocks.size()-1);
		allBlocks.remove(allBlocks.size()-1);
		
		for (CellSpaceInformation pos : codomain.getCells())
			cellRelations.add(getAssociatedCells(allBlocks, pos));
		
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
