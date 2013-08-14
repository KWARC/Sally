package info.kwarc.sally.spreadsheet2;

import java.util.List;

public abstract class Relation {
	
	int id;
	List<Block> blocks;
	
	public Relation(int id, List<Block> blocks) {
		this.id = id;
		this.blocks = blocks;
	}
	

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((blocks == null) ? 0 : blocks.hashCode());
		result = prime * result + id;
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
		if (id != other.id)
			return false;
		return true;
	}

	public int getId() {
		return this.id;
	}
	
	public List<Block> getBlocks() {
		return this.blocks;
	}

}
