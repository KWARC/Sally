package info.kwarc.sally.spreadsheet3.model;

public class RangeInformation {
	String worksheet;
	int startRow, endRow, startCol, endCol;
	
	public RangeInformation(String worksheet, int startRow, int startCol,
			int endRow, int endCol) {
		super();
		
		this.worksheet = worksheet;
		this.startRow = java.lang.Math.min(startRow, endRow);
		this.startCol = java.lang.Math.min(startCol, endCol);
		this.endRow = java.lang.Math.max(startRow, endRow);
		this.endCol = java.lang.Math.max(startCol, endCol);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + endCol;
		result = prime * result + endRow;
		result = prime * result + startCol;
		result = prime * result + startRow;
		result = prime * result
				+ ((worksheet == null) ? 0 : worksheet.hashCode());
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
		RangeInformation other = (RangeInformation) obj;
		if (endCol != other.endCol)
			return false;
		if (endRow != other.endRow)
			return false;
		if (startCol != other.startCol)
			return false;
		if (startRow != other.startRow)
			return false;
		if (worksheet == null) {
			if (other.worksheet != null)
				return false;
		} else if (!worksheet.equals(other.worksheet))
			return false;
		return true;
	}

	public String getWorksheet() {
		return worksheet;
	}

	public int getStartRow() {
		return startRow;
	}

	public int getEndRow() {
		return endRow;
	}

	public int getStartCol() {
		return startCol;
	}

	public int getEndCol() {
		return endCol;
	}
	
}
