package info.kwarc.sally.spreadsheet3.model;

public class CellDependencyDescription {
	
	int minX, maxX, minY, maxY;
	String cellRelation;		// e.g. 0,y;x,0;x,y
	
	public CellDependencyDescription(int minX, int maxX, int minY, int maxY,
			String cellRelation) {
		super();
		this.minX = minX;
		this.maxX = maxX;
		this.minY = minY;
		this.maxY = maxY;
		this.cellRelation = cellRelation;
	}
	
	public CellDependencyDescription(sally.CellDependencyDescriptionMsg msg) {
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
	
	public sally.CellDependencyDescriptionMsg serialize() {
		sally.CellDependencyDescriptionMsg.Builder msg = sally.CellDependencyDescriptionMsg.newBuilder();
		msg.setMinX(this.minX);
		msg.setMaxX(this.maxX);
		msg.setMinY(this.minY);
		msg.setMaxY(this.maxY);
		msg.setCellRelation(this.cellRelation);
		return msg.build();
	}

}
