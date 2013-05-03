package info.kwarc.sally.model.document.spreadsheet;

public class RangeCoordinates {
	
	private CellSpaceInformation startPosition, endPosition;
	private int worksheet;
	
	public RangeCoordinates(int worksheet, CellSpaceInformation startPosition, CellSpaceInformation endPosition) {
		this.worksheet = worksheet;
		this.startPosition = startPosition;
		this.endPosition = endPosition;
	}
	
	public RangeCoordinates(int worksheet, int startRow, int startColumn, int endRow, int endColumn) {
		this(worksheet, new CellSpaceInformation(startRow, startColumn), new CellSpaceInformation(endRow, endColumn));
	}
	
	public RangeCoordinates(CellSpaceInformation cellSpaceInformation, CellSpaceInformation cellSpaceInformation2) {
		this(cellSpaceInformation.getWorksheet(), cellSpaceInformation, cellSpaceInformation2);
		if (cellSpaceInformation.getWorksheet() != cellSpaceInformation2.getWorksheet())
			throw new java.lang.IllegalArgumentException("Start and endposition are on different worksheets.");
	}

	public int getWorksheet() {
		return worksheet;
	}

	public int getStartRow() {
		return startPosition.getRow();
	}

	public int getStartColumn() {
		return startPosition.getColumn();
	}
	
	public CellSpaceInformation getStartPosition() {
		return new CellSpaceInformation(startPosition);
	}
	
	public CellSpaceInformation getEndPosition() {
		return new CellSpaceInformation(endPosition);
	}

	public int getEndRow() {
		return endPosition.getRow();
	}

	public int getEndColumn() {
		return endPosition.getColumn();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((endPosition == null) ? 0 : endPosition.hashCode());
		result = prime * result
				+ ((startPosition == null) ? 0 : startPosition.hashCode());
		result = prime * result + worksheet;
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
		RangeCoordinates other = (RangeCoordinates) obj;
		if (endPosition == null) {
			if (other.endPosition != null)
				return false;
		} else if (!endPosition.equals(other.endPosition))
			return false;
		if (startPosition == null) {
			if (other.startPosition != null)
				return false;
		} else if (!startPosition.equals(other.startPosition))
			return false;
		if (worksheet != other.worksheet)
			return false;
		return true;
	}

	public int getDistanceFrom(CellSpaceInformation pos) {
		int rowDist = java.lang.Math.max(java.lang.Math.max(startPosition.getRow() - pos.getRow(), pos.getRow() - endPosition.getRow()), 0);
		int colDist = java.lang.Math.max(java.lang.Math.max(startPosition.getColumn() - pos.getColumn(), pos.getColumn() - endPosition.getColumn()), 0);
		return java.lang.Math.max(rowDist, colDist);
	}
	
	public sally.CellRange getProtoBufRepresentation() {
		sally.CellRange.Builder cellRangeMsg = sally.CellRange.newBuilder();
		cellRangeMsg.setStart( sally.CellPosition.newBuilder().setSheet(worksheet).setRow(startPosition.getRow()).setCol(startPosition.getColumn()).build() );
		cellRangeMsg.setEnd( sally.CellPosition.newBuilder().setSheet(worksheet).setRow(endPosition.getRow()).setCol(endPosition.getColumn()).build() );
		
		return cellRangeMsg.build();
	}

}
