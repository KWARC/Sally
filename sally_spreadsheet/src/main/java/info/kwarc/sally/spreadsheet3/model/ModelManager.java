package info.kwarc.sally.spreadsheet3.model;


import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Message;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.logic.RelationBuilder;
import info.kwarc.sally.spreadsheet3.logic.RelationInterpreter;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ModelManager {
	
	//FormalSpreadsheet spreadsheet;
	Map<Integer, Block> blocks;
	Map<Integer, Relation> relations;
	int maxBlockID, maxRelationID;
	
	Map<CellSpaceInformation, Block> positionToAtomicBlock;
	Map<CellSpaceInformation, List<Block>> positionToTopLevelBlocks;
	Map<CellSpaceInformation, List<Relation>> positionToRelations;
	
	//IOntologyProvider ontologyInterface;
	
	
	final Logger logger = LoggerFactory.getLogger(ModelManager.class);
	
	/**
	 * Create a new manager for the abstract spreadsheet model.
	 * @param ontologyInterface An interface to access the ontology.
	 */
	public ModelManager() {
		this.blocks = new HashMap<Integer, Block>();
		this.relations = new HashMap<Integer, Relation>();
		this.maxBlockID = 0;
		this.maxRelationID = 0;
		
		positionToAtomicBlock = new HashMap<CellSpaceInformation, Block>();
		positionToTopLevelBlocks = new HashMap<CellSpaceInformation, List<Block>>();
		positionToRelations = new HashMap<CellSpaceInformation, List<Relation>>();
		
		//this.ontologyInterface = ontologyInterface;
	}
	
	/**
	 * Restore a manager for the abstract spreadsheet model from a protobuffer message. 
	 * @param ontologyInterface An interface to access the ontology.
	 * @param modelMsg A protobuffer message that contains all data to restore an abstract spreadsheet model.
	 * @throws ModelException 
	 */
	public ModelManager(sally.ModelDataMsg modelMsg) throws ModelException {
		this.blocks = new HashMap<Integer, Block>();
		this.relations = new HashMap<Integer, Relation>();
		this.maxBlockID = 0;
		this.maxRelationID = 0;
		
		positionToAtomicBlock = new HashMap<CellSpaceInformation, Block>();
		positionToTopLevelBlocks = new HashMap<CellSpaceInformation, List<Block>>();
		positionToRelations = new HashMap<CellSpaceInformation, List<Relation>>();
		
		createBlocks(modelMsg.getBlocksList());
		createRelations(modelMsg.getRelationsList());
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
		result = prime * result + maxBlockID;
		result = prime * result + maxRelationID;
		result = prime
				* result
				+ ((positionToAtomicBlock == null) ? 0 : positionToAtomicBlock
						.hashCode());
		result = prime
				* result
				+ ((positionToTopLevelBlocks == null) ? 0 : positionToTopLevelBlocks.hashCode());
		result = prime
				* result
				+ ((positionToRelations == null) ? 0 : positionToRelations
						.hashCode());
		result = prime * result
				+ ((relations == null) ? 0 : relations.hashCode());
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
		ModelManager other = (ModelManager) obj;
		if (blocks == null) {
			if (other.blocks != null)
				return false;
		} else if (!blocks.equals(other.blocks))
			return false;
		if (maxBlockID != other.maxBlockID)
			return false;
		if (maxRelationID != other.maxRelationID)
			return false;
		if (positionToAtomicBlock == null) {
			if (other.positionToAtomicBlock != null)
				return false;
		} else if (!positionToAtomicBlock.equals(other.positionToAtomicBlock))
			return false;
		if (positionToTopLevelBlocks == null) {
			if (other.positionToTopLevelBlocks != null)
				return false;
		} else if (!positionToTopLevelBlocks.equals(other.positionToTopLevelBlocks))
			return false;
		if (positionToRelations == null) {
			if (other.positionToRelations != null)
				return false;
		} else if (!positionToRelations.equals(other.positionToRelations))
			return false;
		if (relations == null) {
			if (other.relations != null)
				return false;
		} else if (!relations.equals(other.relations))
			return false;
		return true;
	}
	
	// ---------- Methods for the Spreadsheet Annotation Model ----------
	
	// ++++ Block operations ++++
	
	// Block operations - Create, get, remove

	/**
	 * Create an atomic block for a cell. If there is already a block for that cell the function will not create a new one.
	 * @param position The cell position of the atomic block.
	 * @return The block for that was created or already exists for that position.
	 */
	public Block getOrCreateAtomicBlock(CellSpaceInformation position) {
		if (positionToAtomicBlock.containsKey(position))
			return positionToAtomicBlock.get(position);
		else {
			maxBlockID++;
			Block b = new BlockAtomic(maxBlockID, position);
			blocks.put(maxBlockID, b);
			positionToAtomicBlock.put(position, b);
			addPositionToBlockLink(position, b, null);
			return b;
		}
	}
	
	/**
	 * Create a block from existing blocks.
	 * @param subBlocks The new block is a composition of the subBlocks.
	 * @return The new block.
	 */
	public Block createBlock(List<Block> subBlocks) {
		maxBlockID++;
		Block b = new BlockComposed(maxBlockID, subBlocks);
		blocks.put(maxBlockID, b);
	    addPositionsToBlockLink(b.getCells(), b, subBlocks);
		return b;
	}
	
	/**
	 * Create a block for a list of positions. At first a block for each position is created and afterwards a superblock that contains all atomic blocks.
	 * @param positions A list of positions for which the block is created
	 * @return The superblock that contains all atomic blocks.
	 */
	public Block createComposedBlock(List<CellSpaceInformation> positions) {
		List<Block> blocks = new ArrayList<Block>();
		for (CellSpaceInformation pos : positions)
			blocks.add(getOrCreateAtomicBlock(pos));
		return createBlock(blocks);
	}
	
	/**
	 * Return the block with the given ID
	 * @param id The id of the block.
	 * @return The block with the given id or null if no such block exists.
	 */
	public Block getBlockByID(int id) {
		return blocks.get(id);
	}
	
	/**
	 * Get all blocks that contain a certain position.
	 * @param position The position that should be contained in the block.
	 * @return List of all blocks that contain the position
	 */
	public List<Block> getBlocksForPosition(CellSpaceInformation position) {
		return new ArrayList<Block>(positionToTopLevelBlocks.get(position));
	}
	
	/**
	 * Get all blocks that contain at least one cell in the given range.
	 * @param range The range in which blocks should be found.
	 * @return List of blocks that contain at least one cell in the given range.
	 */
	public List<Block> getBlocksInRange(RangeInformation range) {
		List<CellSpaceInformation> positions = Util.expandRange(
				new CellSpaceInformation(range.getWorksheet(), range.getStartRow(), range.getStartCol()),
				new CellSpaceInformation(range.getWorksheet(), range.getEndRow(), range.getEndCol()));
		List<Block> blocks = new ArrayList<Block>();
		
		for (CellSpaceInformation pos : positions) {
			List<Block> found = getBlocksForPosition(pos);
			for (Block b : found)
				if (!blocks.contains(b))
					blocks.add(b);
		}
		
		return blocks;
	}
	
	/**
	 * Get all blocks that are not contained in an other block.	
	 * @return All blocks that are not contained in an other block.	
	 */
	public List<Block> getAllTopLevelBlocks() {
		List<Block> blocks = new ArrayList<Block>();
		for (List<Block> blockList: positionToTopLevelBlocks.values())
			for (Block b : blockList)
				if (!blocks.contains(b))
					blocks.add(b);
		return blocks;
	}
	
	/**
	 * Get all blocks.	
	 * @return All blocks.	
	 */
	public List<Block> getAllBlocks() {
		return new ArrayList<Block>(blocks.values());
	}
	
	/**
	 * Deletes a block.
	 * All relations that are associated with this block are deleted as well.
	 * @param block
	 */
	public void removeBlock(Block block) {
		List<CellSpaceInformation> positions = block.getCells();
		if (block instanceof BlockAtomic) {
			positionToAtomicBlock.remove(positions.get(0));
		}
		
		// Remove position
		for (CellSpaceInformation pos : positions) {
			List<Block> blocks = positionToTopLevelBlocks.get(pos);
			blocks.remove(block);
			if (blocks.isEmpty())
				positionToTopLevelBlocks.remove(pos);
		}
		
		blocks.remove(block.getId());
		
		// Remove as subblock
		for (Block b : blocks.values())
			if (b.contains(block))
				try {
					b.remove(block);
				} catch (ModelException e) {} 	// This can never happen, because of b.contains(block) 
				
		// Remove relations that contain the block
		for (Relation rel : new ArrayList<Relation>(relations.values())) {
			if (rel.getBlocks().contains(block))
				removeRelation(rel);
		}
		
	}
	
	 // Block operations - Change Management
	
	 public List<Message> addCellToBlock(Block block, CellSpaceInformation position) throws ModelException {
		 List<Message> messages = new ArrayList<Message>();
		 
		 // Create subblock and add it to block and update block linking
		 Block atomicBlock = getOrCreateAtomicBlock(position);
		 block.addSubBlock(atomicBlock);
		 List<Block> atomicBlockList = new ArrayList<Block>();
		 atomicBlockList.add(atomicBlock);
		 addPositionToBlockLink(position, block, atomicBlockList);
		 
		 // Delete old type relation
		 List<Relation> typeRelations = getRelationsFor(null, atomicBlock, Relation.RelationType.TYPERELATION);
		 for (Relation r : typeRelations) {
			 messages.add(new Message(Message.MessageType.RelationMsg, Message.MessageSubType.Info, 
					 "Old type-relation for " + position.toString() + " deleted", r.getId()));
			 removeRelation(r);
		 }
		 
		 return messages;
	 }
	 
	
	// Block operations - Helping functions
	
	private void addPositionToBlockLink(CellSpaceInformation position, Block addBlock, List<Block> removeBlocks) {
		if (positionToTopLevelBlocks.containsKey(position)) {
			List<Block> blocksForPos = positionToTopLevelBlocks.get(position);
			for (Block b : removeBlocks)
				if (blocksForPos.contains(b))
					blocksForPos.remove(b);
			if (!blocksForPos.contains(addBlock))
				blocksForPos.add(addBlock);
		} else {
			List<Block> blockList = new ArrayList<Block>();
			blockList.add(addBlock);
			positionToTopLevelBlocks.put(position, blockList);
		}
	}
	
	private void addPositionsToBlockLink(List<CellSpaceInformation> positions, Block addBlock, List<Block> removeBlocks) {
		for (CellSpaceInformation position : positions)
			addPositionToBlockLink(position, addBlock, removeBlocks);
	}
	
	// ++++ Relation operations ++++
	
	/**
	 * Create a relation between blocks.
	 * @see info.kwarc.sally.spreadsheet3.logic.CDDBuilder
	 * @param blocks The blocks between which the relation holds.
	 * @param type The type of the relation.
	 * @param cellDependencyDescriptions A list of objects that describe the relations between the cells of the blocks.
	 * @return The created relation.
	 * @throws ModelException 
	 */
	public Relation createRelation(Relation.RelationType type, List<Block> blocks, List<CellDependencyDescription> cellDependencyDescriptions) throws ModelException {
		maxRelationID++;
		List<CellTuple> cellRelations = RelationBuilder.createCellRelation(blocks, cellDependencyDescriptions);
		
		Relation r = new Relation(maxRelationID, type, blocks, cellRelations, cellDependencyDescriptions);
		this.relations.put(maxRelationID, r);
		for (Block block : blocks )
			addPositionsToRelationLink(block.getCells(), r);
		return r;
	}
	
	public Relation createUnaryRelation(Relation.RelationType type, Block block) throws java.lang.IllegalArgumentException {
		if ( (type == Relation.RelationType.TYPERELATION) && (!getRelationsFor(null, block, Relation.RelationType.TYPERELATION).isEmpty()) )
			throw new java.lang.IllegalArgumentException("Can not create more than one type relation for one block.");
		
		maxRelationID++;
		Relation r = new Relation(maxRelationID, type, block);
		this.relations.put(maxRelationID, r);
		addPositionsToRelationLink(block.getCells(), r);
		return r;
	}
	
	/**
	 * Returns all relations.
	 * @return All relations.
	 */
	public List<Relation> getAllRelations() {
		return new ArrayList<Relation>(relations.values());
	}
	
	/**
	 * Return the relation with the given ID.
	 * @param id The id of the relation.
	 * @return The relation with the given id or null if no such relation exists.
	 */
	public Relation getRelationByID(int id) {
		return relations.get(id);
	}
	
	/**
	 * Return all relations that are related to the given position.
	 * @param position The position which must be part of the relation.  
	 * @return All relations that are related to the given position.
	 */
	public List<Relation> getRelationForPosition(CellSpaceInformation position) {
		List<Relation> relations = positionToRelations.get(position);
		if (relations == null)
			return new ArrayList<Relation>();
		else
			return relations;
	}
	
	public List<Relation> getRelationsFor(CellSpaceInformation position, Block block, Relation.RelationType type) {
		List<Relation> relationList1;
		if (position != null)
			relationList1 = positionToRelations.get(position);
		else
			relationList1 = getAllRelations();
		
		List<Relation> relationList2 = new ArrayList<Relation>();
		for (Relation rel : relationList1) {
			if ( ((block == null) || (rel.getBlocks().contains(block)) ) &&
				 ((type == null) || (rel.getRelationType().equals(type)) ) )
				 relationList2.add(rel);
		}
		return relationList2;
	}
	
	/**
	 * Getting all cell relations that contain the given position.
	 * @param position The position which must be part of the cell relations.
	 * @return All cell relations that contain the given position.
	 */
	public List<CellTuple> getCellRelationsForPosition(CellSpaceInformation position) {
		List<CellTuple> cellRelations = new ArrayList<CellTuple>();
		for (Relation rel : getRelationForPosition(position)) 
				cellRelations.addAll(rel.getCellRelationFor(position));
		
		return cellRelations;
	}


	public void removeRelation(Relation rel) {
		relations.remove(rel.getId());
		for (Block b : rel.getBlocks() ){
			for (CellSpaceInformation pos : b.getCells()) {
				List<Relation> allRelationsForPos = positionToRelations.get(pos);
				allRelationsForPos.remove(rel);
				if (allRelationsForPos.isEmpty())
					positionToRelations.remove(pos);
			}
		}
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
	
	// ---------- Methods for the semantic interpretation ----------
	
	/**
	 * Return the ontology interface for this manager.
	 * @return The Ontology Interface
	 */
	/*public IOntologyProvider getOntologyInterface() {
		return this.ontologyInterface;
	}*/
	
	/**
	 * Get a semantic interpretation for all cells. If a cell is part of a relation, the cell will be interpreted by the semantic of the relation. 
	 * Cells that do not belong to a relation are interpreted by their value interpretation. Therefore at the moment a cell has just one semantic interpretation.
	 * @param spreadsheet
	 * @return A map that maps a cell to its semantic interpretation.
	 * @throws ModelException 
	 */
	public Map<CellSpaceInformation, String> getCompleteSemanticMapping(ConcreteSpreadsheet spreadsheet, IOntologyProvider ontologyInterface) throws ModelException {
		Map<CellSpaceInformation, String> mapping = new HashMap<CellSpaceInformation, String>();
		
		// Value Interpretations
		for (Block block : getAllTopLevelBlocks()) {
			for (CellSpaceInformation pos : block.getCells() ) {
				if (mapping.containsKey(pos))
					throw new java.lang.IllegalStateException("Multiple semantic interpretations for " + pos.toString() + "possible.");
				
				mapping.put(pos, block.getValueInterpretation(spreadsheet.get(pos).getValue()) );	
			}
		}
		
		// Interpretations for functional blocks
		for (Relation rel : this.relations.values()) {
			if (rel.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
				for (CellTuple cellTuple : rel.getCellRelations()) {
					String interpretation = RelationInterpreter.interprete(rel,cellTuple, spreadsheet, ontologyInterface);
					mapping.put(cellTuple.getTuple().get(cellTuple.getTuple().size()-1), interpretation);
				}
			}
		}
	
		return mapping;
	}
	
	
	public Map<Block, String> getBlockTypes(List<Block> blocks) {
		Map<Block, String> blockTypes = new HashMap<Block, String>();
		for (Block b : blocks) {
			List<Relation> typeRelations = getRelationsFor(null, b, Relation.RelationType.TYPERELATION);
			if (typeRelations.size() == 1)
				blockTypes.put(b, typeRelations.get(0).getUri());
		}
		return blockTypes;
	}
	
	/**
	 * Return a protobuffer message that contains all data from the model.
	 * @return A protobuffer message that contains all data from the model.
	 */
	public sally.ModelDataMsg serialize() {
		sally.ModelDataMsg.Builder msg = sally.ModelDataMsg.newBuilder();
		
		for (Block b : this.blocks.values())
			msg.addBlocks(b.serialize());
		
		for (Relation r : this.relations.values())
			msg.addRelations(r.serialize());
		
		return msg.build();
	}
	
	
	private void createBlocks(List<sally.BlockMsg> msgListOrig) throws ModelException {
		List<sally.BlockMsg> msgList = new ArrayList<sally.BlockMsg>(msgListOrig);		// The original list does not support the remove operator
		while (!msgList.isEmpty()) {
			boolean createdBlock = false;
			for (int i = 0; (i < msgList.size()) && !createdBlock; i++) {
				sally.BlockMsg msg = msgList.get(i);
				if (msg.getType().equals(sally.BlockMsg.Type.Atomic)) {
					Block b = Block.createBlockFromMessage(msg, this);
					maxBlockID = java.lang.Math.max(maxBlockID,b.getId());
					blocks.put(b.getId(), b);
					positionToAtomicBlock.put(new CellSpaceInformation(msg.getPosition()), b);
					addPositionToBlockLink(new CellSpaceInformation(msg.getPosition()), b, null);
					msgList.remove(i);
					createdBlock = true;
				} else if (msg.getType().equals(sally.BlockMsg.Type.Composed)) {
					boolean allFound = true;
					for (Integer id : msg.getSubBlockIdsList()) {
						if (!blocks.containsKey(id)) 
							allFound = false;
					}
					if (allFound) {
						Block b = Block.createBlockFromMessage(msg, this);
						maxBlockID = java.lang.Math.max(maxBlockID,b.getId());
						blocks.put(b.getId(), b);
						addPositionsToBlockLink(b.getCells(), b, b.getSubBlocks());
						msgList.remove(i);
						createdBlock = true;
					}
				}
			}
		}
	}
	
	private void createRelations(List<sally.RelationMsg> msgList) throws ModelException {
		for (sally.RelationMsg msg : msgList) {
			Relation r = new Relation(msg, this);
			relations.put(r.getId(), r);
			maxRelationID = java.lang.Math.max(maxRelationID, r.getId());
			for (Block block : r.getBlocks() )
				addPositionsToRelationLink(block.getCells(), r);
		}
	}
	

}
