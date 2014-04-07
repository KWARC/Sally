package info.kwarc.sally.spreadsheet3.model;

public class CellDependencyDescription {
	
	int minX, maxX, minY, maxY;
	String cellRelation;		// e.g. 0,y;x,0;x,y
	
	/**
	 * Creates an object to describe the relation of cells between different blocks by describing the dependencies of the indices.
	 * Example: The description 0,y;x,0;x,y provides the relation between 3 block, one index tuple for each block separated by ';'. The description can be
	 * expanded to the list [(0,0),(0,0),(0,0)], [(0,0),(1,0),(1,0)], ...,[(0,0),(maxX,0),(maxX,0)], [(0,1),(0,0),(0,1)], [(0,1),(1,0),(1,1)], ...,[(0,1),(maxX,0),(maxX,1)],
	 *                      ...,[(0,maxY),(0,0),(0,maxY)], [(0,maxY),(1,0),(1,maxY)], ...,[(0,maxY),(maxX,0),(maxX,maxY)].
     * A relation will map such a list to concrete block indices, whereby the offset of a block will be added to a cell tuple. In example, a block with
     * an upper left border in C5 has the offset (4,2) and a tuple (1,2) will therefore be mapped to the the block entry on position (5,4) which is E6.
     * @see info.kwarc.sally.spreadsheet3.logic.CDDBuilder
	 */
	public CellDependencyDescription(int minX, int maxX, int minY, int maxY,
			String cellRelation) {
		super();
		this.minX = minX;
		this.maxX = maxX;
		this.minY = minY;
		this.maxY = maxY;
		this.cellRelation = cellRelation;
	}
	
	public CellDependencyDescription(Sally.CellDependencyDescriptionMsg msg) {
		this.minX = msg.getMinX();
		this.maxX = msg.getMaxX();
		this.minY = msg.getMinY();
		this.maxY = msg.getMaxY();
		this.cellRelation = msg.getCellRelation();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((cellRelation == null) ? 0 : cellRelation.hashCode());
		result = prime * result + maxX;
		result = prime * result + maxY;
		result = prime * result + minX;
		result = prime * result + minY;
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
		CellDependencyDescription other = (CellDependencyDescription) obj;
		if (cellRelation == null) {
			if (other.cellRelation != null)
				return false;
		} else if (!cellRelation.equals(other.cellRelation))
			return false;
		if (maxX != other.maxX)
			return false;
		if (maxY != other.maxY)
			return false;
		if (minX != other.minX)
			return false;
		if (minY != other.minY)
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		return "(" + this.minX + "/" + this.minY + " - " + this.maxX + "/" + this.maxY + "): " + this.cellRelation;
	}

	public int getMinX() {
		return minX;
	}
	public int getMaxX() {
		return maxX;
	}
	public int getMinY() {
		return minY;
	}
	public int getMaxY() {
		return maxY;
	}
	public String getCellRelation() {
		return cellRelation;
	}
	
	public Sally.CellDependencyDescriptionMsg serialize() {
		Sally.CellDependencyDescriptionMsg.Builder msg = Sally.CellDependencyDescriptionMsg.newBuilder();
		msg.setMinX(this.minX);
		msg.setMaxX(this.maxX);
		msg.setMinY(this.minY);
		msg.setMaxY(this.maxY);
		msg.setCellRelation(this.cellRelation);
		return msg.build();
	}

}
