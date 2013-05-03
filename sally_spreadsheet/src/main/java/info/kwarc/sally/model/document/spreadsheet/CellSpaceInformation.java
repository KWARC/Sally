package info.kwarc.sally.model.document.spreadsheet;

import java.util.List;

public class CellSpaceInformation {
	private int worksheet, row, column, width, height;
	
	public CellSpaceInformation(int worksheet, int row, int column, int width, int height) {
		this.worksheet = worksheet;
		this.row = row;
		this.column = column;
		this.width = width;
		this.height = height;
	}
	
	public CellSpaceInformation(int worksheet, int row, int column) {
		this(worksheet, row, column, 1, 1);
	}

	public CellSpaceInformation(int row, int column) {
		this(-1, row, column, 1, 1);
	}
	
	public CellSpaceInformation(CellSpaceInformation ci) {
		this(ci.getWorksheet(), ci.getRow(), ci.getColumn(), ci.getWidth(),ci.getHeight() );
	}
	
	public CellSpaceInformation(sally.CellSpaceInformation msg) {
		this( msg.getPosition().getSheet(),  msg.getPosition().getRow(),  msg.getPosition().getCol(), msg.getWidth(), msg.getHeight());	
	}
	
	public CellSpaceInformation(sally.CellPosition msg) {
		this( msg.getSheet(), msg.getRow(), msg.getCol());
	}
	
	

	@Override
	public String toString() {
		String result = "(" + worksheet + ":" + row + "/" + column;
		if ((height > 1) || (width > 1))
			result += " - " + (row+height-1) + "/" + (column+width-1);
		result += ")";
		return result;
	}
	

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + column;
		result = prime * result + row;
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
		CellSpaceInformation other = (CellSpaceInformation) obj;
		if (column != other.column)
			return false;
		if (row != other.row)
			return false;
		if (worksheet != other.worksheet)
			return false;
		return true;
	}

	public int getWorksheet() {
		return worksheet;
	}

	public int getRow() {
		return row;
	}

	public int getColumn() {
		return column;
	}
	
	public int getWidth() {
		return width;
	}
	
	public int getHeight() {
		return height;
	}
	
	public void add(CellSpaceInformation c) {
		if ((this.getWorksheet() == c.getWorksheet()) || (c.getWorksheet() == -1) ) {
			row += c.getRow();
			column += c.getColumn();
		} else
			throw new java.lang.IllegalArgumentException("Could not add CellSpaceInformation with a different worksheet.");
	}
	
	public boolean isAssociated(CellSpaceInformation pos) {
		if (pos.getWorksheet() != getWorksheet())
			return false;
		if ( (pos.getColumn() >= getColumn()) && (pos.getColumn() < getColumn() + getWidth()) )
			return true;
		if ( (getColumn() >= pos.getColumn()) && (getColumn() < pos.getColumn() + pos.getWidth()))
			return true;
		if ( (pos.getRow() >= getRow()) && (pos.getRow() < getRow() + getHeight()) )
			return true;
		if ( (getRow() >= pos.getRow()) && (getRow() < pos.getRow() + pos.getHeight()))
			return true;
		
		return false;
	}
	
	public boolean isAssociated(List<CellSpaceInformation> positions) {
		boolean assoc = true;
		for (CellSpaceInformation pos : positions)
			if (!isAssociated(pos))
				assoc = false;
		return assoc;
	}
	
	public sally.CellSpaceInformation getProtoBufRepresentation() {
		sally.CellSpaceInformation.Builder msgBuilder = sally.CellSpaceInformation.newBuilder();
		sally.CellPosition.Builder msgPositionBuilder = sally.CellPosition.newBuilder();
		msgPositionBuilder.setSheet(worksheet);
		msgPositionBuilder.setRow(row);
		msgPositionBuilder.setCol(column);
		msgBuilder.setPosition(msgPositionBuilder.build());
		msgBuilder.setHeight(height);
		msgBuilder.setWidth(width);
		
		return msgBuilder.build();
	}
}
