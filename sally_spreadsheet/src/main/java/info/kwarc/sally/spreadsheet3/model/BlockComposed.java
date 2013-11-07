package info.kwarc.sally.spreadsheet3.model;

import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretation;

import java.util.ArrayList;
import java.util.List;

public class BlockComposed extends Block {
	
	List<Block> blocks;
	
	public BlockComposed(int id, List<Block> blocks) {
		super(id, blocks.get(0).getWorksheet());
		for (Block b : blocks)
			if (!b.getWorksheet().equals(this.worksheet))
				throw new java.lang.IllegalArgumentException("Can not compose blocks from different worksheets to one block.");
		this.blocks = new ArrayList<Block>(blocks);
	}
	
	public BlockComposed(int id, List<Block> blocks, List<ValueInterpretation> valueInterpretations) {
		super(id, blocks.get(0).getWorksheet(), valueInterpretations);
		for (Block b : blocks)
			if (!b.getWorksheet().equals(this.worksheet))
				throw new java.lang.IllegalArgumentException("Can not compose blocks from different worksheets to one block.");
		this.blocks = new ArrayList<Block>(blocks);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
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
		BlockComposed other = (BlockComposed) obj;
		if (blocks == null) {
			if (other.blocks != null)
				return false;
		} else if (!blocks.equals(other.blocks))
			return false;
		return true;
	}

	@Override
	public List<CellSpaceInformation> getCells() {
		List<CellSpaceInformation> cells = new ArrayList<CellSpaceInformation>();
		for (Block b : blocks)
			cells.addAll(b.getCells());
		return cells;
	}
	
	public List<Block> getSubBlocks() {
		return new ArrayList<Block>(blocks);
	}
	
	@Override
	public boolean contains(Block b) {
		return blocks.contains(b);
	}
	
	@Override
	public void remove(Block b) {
		blocks.remove(b);
	}
	
	@Override
	public int getMinRow() {
		int min = Integer.MAX_VALUE;
		for (Block b : this.getSubBlocks())
			min = java.lang.Math.min(min, b.getMinRow());
		return min;
	}
	
	@Override
	public int getMaxRow() {
		int max = Integer.MIN_VALUE;
		for (Block b : this.getSubBlocks())
			max = java.lang.Math.max(max, b.getMaxRow());
		return max;
	}
	
	@Override
	public int getMinColumn() {
		int min = Integer.MAX_VALUE;
		for (Block b : this.getSubBlocks())
			min = java.lang.Math.min(min, b.getMinColumn());
		return min;
	}
	
	@Override
	public int getMaxColumn() {
		int max = Integer.MIN_VALUE;
		for (Block b : this.getSubBlocks())
			max = java.lang.Math.max(max, b.getMaxColumn());
		return max;
	}
	
	@Override
	public sally.BlockMsg serialize() {
		sally.BlockMsg.Builder blockMsg = sally.BlockMsg.newBuilder();
		blockMsg.setType(sally.BlockMsg.Type.Composed);
		blockMsg.setId(this.id);
		blockMsg.setWorksheet(this.worksheet);
		for (ValueInterpretation vi : this.valueInterpretations)
			blockMsg.addValueInterpretations(vi.serialize());
		
		for (PropertyName p : properties.keySet())
			blockMsg.addProperties(sally.Property.newBuilder().setPropertyID(p.ordinal()).setValue(properties.get(p)).build() );
		
		for (Block b : this.blocks)
			blockMsg.addSubBlockIds(b.getId());
		return blockMsg.build();
	}

}
