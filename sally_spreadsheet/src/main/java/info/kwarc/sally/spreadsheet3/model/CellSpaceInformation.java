package info.kwarc.sally.spreadsheet3.model;

import java.util.List;

public class CellSpaceInformation {
	private String worksheet; 
	private int row, column, height, width;
	
	public CellSpaceInformation(String worksheet, int row, int column, int height, int width) {
		this.worksheet = worksheet;
		this.row = row;
		this.column = column;
		this.width = width;
		this.height = height;
	}
	
	public CellSpaceInformation(String worksheet, int row, int column) {
		this(worksheet, row, column, 1, 1);
	}

	public CellSpaceInformation(int row, int column) {
		this("", row, column, 1, 1);
	}
	
	public CellSpaceInformation(CellSpaceInformation ci) {
		this(ci.getWorksheet(), ci.getRow(), ci.getColumn(), ci.getWidth(),ci.getHeight() );
	}
	
	public CellSpaceInformation(sally.CellSpaceInformationMsgNew msg) {
		this.worksheet = msg.getWorksheet();
		this.row = msg.getRow();
		this.column = msg.getColumn();
		
		if (msg.hasHeight())
			this.height = msg.getHeight();
		else
			this.height = 1;
		
		if (msg.hasWidth())
			this.width = msg.getWidth();
		else
			this.width = 1;
	}
	

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + column;
		result = prime * result + row;
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
		CellSpaceInformation other = (CellSpaceInformation) obj;
		if (column != other.column)
			return false;
		if (row != other.row)
			return false;
		if (worksheet == null) {
			if (other.worksheet != null)
				return false;
		} else if (!worksheet.equals(other.worksheet))
			return false;
		return true;
	}

	@Override
	public String toString() {
		String result = "(" + worksheet + ":" + row + "/" + column;
		if ((height > 1) || (width > 1))
			result += " - " + (row+height-1) + "/" + (column+width-1);
		result += ")";
		return result;
	}
	
	public String getWorksheet() {
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
		if ( this.getWorksheet().equals( c.getWorksheet())  || c.getWorksheet().isEmpty() ) {
			row += c.getRow();
			column += c.getColumn();
		} else
			throw new java.lang.IllegalArgumentException("Could not add CellSpaceInformation with a different worksheet.");
	}
	
	public boolean isAssociated(CellSpaceInformation pos) {
		if (!pos.getWorksheet().equals(this.getWorksheet()) )
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
	
	public sally.CellSpaceInformationMsgNew serialize() {
		sally.CellSpaceInformationMsgNew.Builder msg = sally.CellSpaceInformationMsgNew.newBuilder();
		msg.setWorksheet(this.worksheet);
		msg.setRow(this.row);
		msg.setColumn(this.column);
		msg.setHeight(this.height);
		msg.setWidth(this.width);
		return msg.build();
	}

}
