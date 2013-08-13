package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class BlockComposed extends Block {
	
	List<Block> blocks;
	
	public BlockComposed(int id, List<Block> blocks) {
		super(id);
		this.blocks = blocks;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
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

}
