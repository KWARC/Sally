package info.kwarc.sally.spreadsheet3.extraction;


import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.util.HashMap;
import java.util.Map;

public class Sheet {
	String sheet;
	int maxRow, maxColumn;
	Map<CellSpaceInformation, Cell> cells;
	
	public Sheet(String id) {
		super();
		this.sheet = id;
		this.maxRow = 0;
		this.maxColumn = 0;
		this.cells = new HashMap<CellSpaceInformation, Cell>();
	}
	
	public void addCell(Cell cell) {
		if (cell.getPosition().getWorksheet() == sheet) {
			CellSpaceInformation pos = cell.getPosition();
			cells.put(pos, cell);
			maxRow = java.lang.Math.max(pos.getRow()+1, maxRow);
			maxColumn = java.lang.Math.max(pos.getColumn()+1, maxColumn);
		 
			for (int row = pos.getRow(); row < pos.getRow() + pos.getHeight(); row++) {
				for (int column = pos.getColumn(); column < pos.getColumn() + pos.getWidth(); column++) {
					if ((row > pos.getRow()) || (column > pos.getColumn()) ) {
						CellSpaceInformation newPosition = new CellSpaceInformation(sheet, row, column);
						if (!cells.containsKey(newPosition))
							cells.put(newPosition, new Cell(newPosition));
						else 
							cells.get(newPosition).isHidden(true);
					}
				}
			}
			
		} else
			throw new java.lang.IllegalArgumentException("Cell has an invalid worksheet id: " + cell.getPosition().getWorksheet());
	}
	
	public Cell getCellForPosition(int row, int column) {
		return cells.get(new CellSpaceInformation(sheet, row, column));
	}
	
	public String getId() {
		return sheet;
	}

	public int getMaxRow() {
		return maxRow;
	}

	public int getMaxColumn() {
		return maxColumn;
	}

}
