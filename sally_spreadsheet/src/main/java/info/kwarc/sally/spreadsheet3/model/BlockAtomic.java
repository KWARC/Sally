package info.kwarc.sally.spreadsheet3.model;

import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretation;

import java.util.ArrayList;
import java.util.List;

/**
 * Atomic blocks contain only one cell.
 * @author cliguda
 *
 */
public class BlockAtomic extends Block {
	
	CellSpaceInformation position;
	
	public BlockAtomic(int id, CellSpaceInformation position) {
		super(id, position.getWorksheet());
		this.position = position;
	}
	
	public BlockAtomic(int id, CellSpaceInformation position, List<ValueInterpretation> valueInterpretations) {
		super(id, position.getWorksheet(), valueInterpretations);
		this.position = position;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((position == null) ? 0 : position.hashCode());
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
		BlockAtomic other = (BlockAtomic) obj;
		if (position == null) {
			if (other.position != null)
				return false;
		} else if (!position.equals(other.position))
			return false;
		return true;
	}

	@Override
	public List<CellSpaceInformation> getCells() {
		List<CellSpaceInformation> cells = new ArrayList<CellSpaceInformation>();
		cells.add(position);
		return cells;
	}
	
	@Override
	public List<Block> getSubBlocks() {
		return new ArrayList<Block>();
	}
	
	@Override
	public void addSubBlock(Block subblock) throws ModelException {
		throw new ModelException("Can not add a subblock to an atomic block.");
	}
	
	@Override
	public boolean contains(Block b) {
		return false;
	}
	
	@Override
	public void remove(Block b) throws ModelException {
		throw new ModelException("Can not remove a block from an atomic block.");
	}
	
	@Override
	public int getMinRow() {
		int min = Integer.MAX_VALUE;
		for (CellSpaceInformation pos : this.getCells())
			min = java.lang.Math.min(min, pos.getRow());
		return min;
	}
	
	@Override
	public int getMaxRow() {
		int max = Integer.MIN_VALUE;
		for (CellSpaceInformation pos : this.getCells())
			max = java.lang.Math.max(max, pos.getRow());
		return max;
	}
	
	@Override
	public int getMinColumn() {
		int min = Integer.MAX_VALUE;
		for (CellSpaceInformation pos : this.getCells())
			min = java.lang.Math.min(min, pos.getColumn());
		return min;
	}
	
	@Override
	public int getMaxColumn() {
		int max = Integer.MIN_VALUE;
		for (CellSpaceInformation pos : this.getCells())
			max = java.lang.Math.max(max, pos.getColumn());
		return max;
	}

	@Override
	public sally.BlockMsg serialize() {
		sally.BlockMsg.Builder blockMsg = sally.BlockMsg.newBuilder();
		blockMsg.setType(sally.BlockMsg.Type.Atomic);
		blockMsg.setId(this.id);
		blockMsg.setWorksheet(this.worksheet);
		for (ValueInterpretation vi : this.valueInterpretations)
			blockMsg.addValueInterpretations(vi.serialize());
		
		for (PropertyName p : properties.keySet())
			blockMsg.addProperties(sally.Property.newBuilder().setPropertyID(p.ordinal()).setValue(properties.get(p)).build() );
		
		blockMsg.setPosition(this.position.serialize());
		return blockMsg.build();
	}

}