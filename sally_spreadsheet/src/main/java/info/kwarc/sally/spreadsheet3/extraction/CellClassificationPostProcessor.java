package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;



public class CellClassificationPostProcessor {
	
	public static void processCell(Sheet sheet, Cell cell, CellAttributeInformation[][] cellInformation) {
		expandHiddenCellPattern(sheet, cell, cellInformation);
		hiddenCellPattern(cell, cellInformation);
		//missingLegendFBStartPattern(cell, cellInformation);
	}
	
	/*public static void processCell(Cell cell, CellAttributeInformation[][] cellInformation) {
		hiddenCellPattern(cell, cellInformation);
		legendOrHeaderPattern(cell, cellInformation);
		missingLegendFBStartPattern(cell, cellInformation);
		theMobIsRightPattern(cell, cellInformation);
	}*/
	
	public static void processSheet(CellAttributeInformation[][] cellInformation, Sheet sheet) {
		for (int row = 0; row < cellInformation.length; row++) {
			for (int column = 0; column < cellInformation[row].length; column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if (cell != null) {
					theMobIsRightPattern(cell, cellInformation);
					//legendOrHeaderPattern(cell, cellInformation);
				}
			}
		}
	}
	
	
	/*public static void processSheet(CellAttributeInformation[][] cellInformation, Sheet sheet) {
		// Find legend headers
		for (int row = 0; row < cellInformation.length; row++) {
			for (int column = 0; column < cellInformation[row].length; column++) {
				// Find further Legendheaders
				if ( (cellInformation[row][column].getCellType() == StructureType.LEGEND) &&
				      (!CellAttributeInformationUtil.hasAssocFB(cellInformation, row, column)) )
					cellInformation[row][column].setCellType( StructureType.LEGENDHEADER );
				
				// Convert hidden cells to original type
				CellSpaceInformation cellPos = sheet.getCellForPosition(row, column).getPosition();
				
				for(int i = row; i < row + cellPos.getHeight(); i++) {
					for (int j = column; j < column + cellPos.getWidth(); j++) {
						if ((i > row) || (j > column) )
								cellInformation[i][j].setCellType( cellInformation[row][column].getCellType() ) ;
					}
				}
			}
		}
	}*/
	
	private static void expandHiddenCellPattern(Sheet sheet, Cell cell, CellAttributeInformation[][] cellInformation) {
		// Convert hidden cells to original type
		CellSpaceInformation cellPos = cell.getPosition();
		int row = cellPos.getRow();
		int column = cellPos.getColumn();
		StructureType t = cellInformation[row][column].getCellType();
		for(int i = row; i < row + cellPos.getHeight(); i++) {
			for (int j = column; j < column + cellPos.getWidth(); j++) {
				if ((i > row) || (j > column) ) {
					CellAttributeInformation cellAttribute = cellInformation[i][j];
					
					if (cellAttribute == null)
						cellAttribute = CellAttributeInformationUtil.createLocalAttributes(sheet, row, column, t);
					else
						cellAttribute.setCellType(t);
				}
			}
		}
	}
	
	/* Discarded
	public static void findMissingLegend(CellAttributeInformation[][] cellInformation, Boolean[][] missingLegend, int startRow, int startColumn) {
		// Search row for available legends
		Boolean legendInRow = false;
		for (int column = startColumn; column < cellInformation[startRow].length; column++)
			if (cellInformation[startRow][column].getCellType().equals(StructureType.LEGEND))
				legendInRow = true;
		if (legendInRow) {
			for (int column = startColumn; column < cellInformation[startRow].length; column++)
				missingLegend[startRow][column] = true;
		}
		
		// Search column for available legends
	}*/
	
	
	private static void hiddenCellPattern(Cell cell, CellAttributeInformation[][] cellInformation) {
		CellSpaceInformation pos = cell.getPosition();
		if ( cellInformation[pos.getRow()][pos.getColumn()].getCellType().equals(StructureType.LEGEND) && 
			(pos.getWidth() > 1) && (pos.getRow() < cellInformation.length-1)) {
			// Counting unknown cells in the next row
			int unknownCells = 0;
			for (int i = 0; i < pos.getWidth(); i++)
				if (cellInformation[pos.getRow()+1][pos.getColumn()+i].getCellType().equals(StructureType.UNKNOWN) )
					unknownCells++;
			if (unknownCells > 1)
				for (int i = 0; i < pos.getWidth(); i++)
					setIfUnknown(new CellSpaceInformation(pos.getRow()+1, pos.getColumn()+i), cellInformation, StructureType.LEGEND);
		}
		if ( cellInformation[pos.getRow()][pos.getColumn()].getCellType().equals(StructureType.LEGEND) && 
				(pos.getHeight() > 1) && (pos.getColumn() < cellInformation[pos.getRow()].length-1)) {
				// Counting unknown cells in the next column
				int unknownCells = 0;
				for (int i = 0; i < pos.getHeight(); i++)
					if (cellInformation[pos.getRow()+i][pos.getColumn()+1].getCellType().equals(StructureType.UNKNOWN))
						unknownCells++;
				if (unknownCells > 1)
					for (int i = 0; i < pos.getHeight(); i++)
						setIfUnknown(new CellSpaceInformation(pos.getRow()+i, pos.getColumn()+1), cellInformation, StructureType.LEGEND);
				
			}
	}
	
	/*private static void legendOrHeaderPattern(Cell cell, CellAttributeInformation[][] cellInformation) {
		CellSpaceInformation pos = cell.getPosition();
		CellSpaceInformation[] posChangings = new CellSpaceInformation[4];
		posChangings[0] = new CellSpaceInformation(0,-1);
		posChangings[1] = new CellSpaceInformation(-1,0);
		posChangings[2] = new CellSpaceInformation(0,1);
		posChangings[3] = new CellSpaceInformation(1,1);
		
		if ( cellInformation[pos.getRow()][pos.getColumn()].getCellType().equals(StructureType.LEGEND) ) {
			Boolean[] sameBoltAsNeighbours = new Boolean[4];
			Boolean[] sameUnderlineStyleAsNeighbours = new Boolean[4];
			Boolean[] sameItalicStyleAsNeighbours = new Boolean[4];
			//Boolean[] sameColorAsNeighbours = new Boolean[4];
			
			for (int i = 0; i < 4; i++) {
				CellSpaceInformation neighbour = new CellSpaceInformation(pos);
				neighbour.add(posChangings[i]);
				if (isAvailable(neighbour, cellInformation) && (cellInformation[pos.getRow()][pos.getColumn()].isBold.equals(cellInformation[neighbour.getRow()][neighbour.getColumn()].isBold)))
					sameBoltAsNeighbours[i] = true;
				else
					sameBoltAsNeighbours[i] = false;
				
				if (isAvailable(neighbour, cellInformation) && (cellInformation[pos.getRow()][pos.getColumn()].isItalic.equals(cellInformation[neighbour.getRow()][neighbour.getColumn()].isItalic)))
					sameItalicStyleAsNeighbours[i] = true;
				else
					sameItalicStyleAsNeighbours[i] = false;	
				
				if (isAvailable(neighbour, cellInformation) && (cellInformation[pos.getRow()][pos.getColumn()].isUnderlined.equals(cellInformation[neighbour.getRow()][neighbour.getColumn()].isUnderlined)))
					sameUnderlineStyleAsNeighbours[i] = true;
				else
					sameUnderlineStyleAsNeighbours[i] = false;
			}
			
			if (isAllFalse(sameBoltAsNeighbours) || isAllFalse(sameUnderlineStyleAsNeighbours) || isAllFalse(sameItalicStyleAsNeighbours))
				cellInformation[pos.getRow()][pos.getColumn()].setCellType(StructureType.LEGENDHEADER);
		}
	}*/
	
	/*private static void missingLegendFBStartPattern(Cell cell, CellAttributeInformation[][] cellInformation) {
		int row = cell.getPosition().getRow();
		int column = cell.getPosition().getColumn();
		if (cellInformation[row][column].getCellType().equals(StructureType.EMPTY) 
				&& isAvailable(new CellSpaceInformation(row-1, column+1), cellInformation) 
				&& isAvailable(new CellSpaceInformation(row, column+1), cellInformation) ) {
			if (cellInformation[row-1][column+1].getCellType().equals(StructureType.LEGEND))
				setIfUnknown(new CellSpaceInformation(row, column+1), cellInformation, StructureType.FB);
			else if (cellInformation[row-1][column+1].getCellType().equals(StructureType.LEGENDHEADER))
				setIfUnknown(new CellSpaceInformation(row, column+1), cellInformation, StructureType.LEGEND);
		}
	}*/
	
	private static void theMobIsRightPattern(Cell cell, CellAttributeInformation[][] cellInformation) {
		int row = cell.getPosition().getRow();
		int column = cell.getPosition().getColumn();
		if (cellInformation[row][column].getCellType().equals(StructureType.FB) 
				&& isAvailable(new CellSpaceInformation(row, column-1), cellInformation) 
				&& isAvailable(new CellSpaceInformation(row, column+1), cellInformation) 
				&& cellInformation[row][column-1].getCellType().equals(StructureType.LEGEND)
				&& cellInformation[row][column+1].getCellType().equals(StructureType.LEGEND))
			cellInformation[row][column].setCellType(StructureType.LEGEND);
		if (cellInformation[row][column].getCellType().equals(StructureType.FB) 
				&& isAvailable(new CellSpaceInformation(row-1, column), cellInformation) 
				&& isAvailable(new CellSpaceInformation(row+1, column), cellInformation) 
				&& cellInformation[row-1][column].getCellType().equals(StructureType.LEGEND)
				&& cellInformation[row+1][column].getCellType().equals(StructureType.LEGEND))
			cellInformation[row][column].setCellType(StructureType.LEGEND);
	}
	
	private static Boolean isAvailable(CellSpaceInformation pos, CellAttributeInformation[][] cellInformation) {
		int row = pos.getRow();
		int column = pos.getColumn();
		return ((row >= 0) && (row < cellInformation.length) &&
			(column >= 0) && (column < cellInformation[row].length) &&
			(cellInformation[row][column] != null) &&
			(!cellInformation[row][column].getCellType().equals(StructureType.EMPTY)) &&
			(!cellInformation[row][column].getCellType().equals(StructureType.HIDDEN)) );
	}
	
	private static void setIfUnknown(CellSpaceInformation pos, CellAttributeInformation[][] cellInformation, StructureType type) {
		int row = pos.getRow();
		int column = pos.getColumn();
		if ((row >= 0) && (row < cellInformation.length) &&
			(column >= 0) && (column < cellInformation[row].length) &&
			(cellInformation[row][column] != null) && (cellInformation[row][column].getCellType().equals(StructureType.UNKNOWN)) )
			cellInformation[row][column].setCellType(type);
	}
	
	/*private static Boolean isAllFalse(Boolean[] array) {
		Boolean result = true;
		for (int i = 0; i < array.length; i++)
			if (array[i].equals(true))
				result = false;
		return result;
	}*/


}
