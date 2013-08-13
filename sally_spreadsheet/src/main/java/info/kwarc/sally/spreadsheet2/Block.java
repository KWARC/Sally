package info.kwarc.sally.spreadsheet2;

import java.util.List;

public abstract class Block {
	
	int id;
	
	public Block(int id) {
		this.id = id;
	}
	
	abstract public int hashCode();
	
	abstract public boolean equals(Object obj);
	
	public int getId() {
		return this.id;
	}
	
	abstract public List<CellSpaceInformation> getCells();

}
