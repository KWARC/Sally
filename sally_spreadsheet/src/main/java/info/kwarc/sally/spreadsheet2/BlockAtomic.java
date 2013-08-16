package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

class BlockAtomic extends Block {
	
	CellSpaceInformation position;
	
	public BlockAtomic(int id, CellSpaceInformation position) {
		super(id);
		this.position = position;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((position == null) ? 0 : position.hashCode());
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

}