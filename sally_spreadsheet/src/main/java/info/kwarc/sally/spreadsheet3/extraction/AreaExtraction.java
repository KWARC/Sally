package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.util.HashMap;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class provides methods to find areas of the same type with the same layout features in spreadsheets.
 * @author cliguda
 *
 */
public class AreaExtraction {
	
	final static int DEFAULTBACKGOUNDCOLOR = 0;
	final static Logger log = LoggerFactory.getLogger(AreaExtraction.class);
	//final static psf.ParserInterface parser = new psf.ParserInterface();		// Needed to compare cell formulae
	
	/**
	 * Extracts areas of the same type and layout features from spreadsheets.
	 * @param sheet The actual worksheet.
	 * @param sheetName The name of of the worksheet.
	 * @param startID The IDs of found areas will start at startID.
	 * @param cellFeatures An array of cellfeatures for the worksheet
	 * @param features A Map for layout features.
	 * @return
	 */
	public static AEResults extractAreas(Sheet sheet, String sheetName, int startID, CellAttributeInformation[][] cellFeatures, FeatureMaps features) {
				
		AEResults results = new AEResults(sheetName, cellFeatures.length, cellFeatures[0].length);
				
		int id = startID;
		
		for (int row = 0; row < cellFeatures.length; row++) {
			for (int column = 0; column < cellFeatures[row].length; column++) {
				if (cellFeatures[row][column].getCellType() == StructureType.LEGEND && !results.hasId(row, column) ) {
					AEResults areas = extractLegendArea(sheetName, cellFeatures, id, row, column, features);
					results.add(areas);
					id = areas.getMaxIndex() + 1;
				} else if (cellFeatures[row][column].getCellType() == StructureType.FB && !results.hasId(row, column) ) {
					AEResults areas = extractFBArea(sheetName, cellFeatures, id, row, column, features);
					//System.out.println("Found a new FB:");
					//areas.print();
					results.add(areas);
					id = areas.getMaxIndex() + 1;
				} else if (cellFeatures[row][column].getCellType() == StructureType.LEGENDHEADER && !results.hasId(row, column)) {
					CellSpaceInformation cellPos = sheet.getCellForPosition(row, column).getPosition();
					results.addArea(new AreaInformation(StructureType.LEGENDHEADER, id, new RangeCoordinates(sheetName, row,column, 
							(row+cellPos.getHeight()-1), (column+cellPos.getWidth()-1))) );
					id++;
				}
			}
		}
		
		return results;
	}
	
	private static AEResults extractLegendArea(String sheet, CellAttributeInformation[][] cellFeatures, int id, int startRow, int startColumn, FeatureMaps features ) {
		AEResults idMap = new AEResults(sheet, cellFeatures.length, cellFeatures[0].length);
		int startIndex = id;
				
		if (cellFeatures[startRow][startColumn].getCellType() != StructureType.LEGEND)
			return idMap;
		
		// Expand area to the right and then to the bottom
		int endColumn1 = startColumn;
		while ( (endColumn1+1 < cellFeatures[startRow].length) &&
				features.sameFeatures(startRow, startColumn, startRow, endColumn1+1) &&
				( (cellFeatures[startRow][endColumn1+1].getCellType() == StructureType.LEGEND) || 
				  (cellFeatures[startRow][endColumn1+1].getCellType() == StructureType.EMPTY) ) )
			endColumn1++;
		
		// Now expand to the bottom
		int endRow1 = startRow;
		//Boolean expand = true;
		Boolean allValid = true;
		while (allValid && (endRow1+1 < cellFeatures.length)) {
			//Boolean legendFound = false;
			for(int j = startColumn; j <= endColumn1; j++) {
				if ( ( (cellFeatures[endRow1+1][j].getCellType() != StructureType.LEGEND) && 
					   (cellFeatures[endRow1+1][j].getCellType() != StructureType.EMPTY) ) ||
					   !features.sameFeatures(startRow, startColumn, endRow1+1, j ) )
					allValid = false;
				//if ( cellFeatures[endRow1+1][j].getCellType() == StructureType.LEGEND)
					//legendFound = true;
			}
			if (allValid)
				endRow1++;
		}
		
		CellSpaceInformation endOfArea = cuttingToFit(cellFeatures, startRow, startColumn, endRow1, endColumn1);
		endRow1 = endOfArea.getRow();
		endColumn1 = endOfArea.getColumn();
		
		// Expand area to the bottom and then to the right
		int endRow2 = startRow;
		while ( (endRow2+1 < cellFeatures.length) &&
				features.sameFeatures(startRow, startColumn, endRow2+1, startColumn) &&
				( (cellFeatures[endRow2+1][startColumn].getCellType() == StructureType.LEGEND) || 
				  (cellFeatures[endRow2+1][startColumn].getCellType() == StructureType.EMPTY) ) )
			endRow2++;
		
			
		// Now expand to the right
		int endColumn2 = startColumn;
		
		allValid = true;
		while (allValid && (endColumn2+1 < cellFeatures[endRow2].length)) {
			//Boolean legendFound = false;
			for(int j = startRow; j <= endRow2; j++) {
				if ( ( (cellFeatures[j][endColumn2+1].getCellType() != StructureType.LEGEND) && 
					   (cellFeatures[j][endColumn2+1].getCellType() != StructureType.EMPTY) ) ||
					   !features.sameFeatures(startRow, startColumn, j, endColumn2+1 ) )
					allValid = false;
			
			}
			if (allValid)
				endColumn2++;
		}
		
		CellSpaceInformation endOfArea2 = cuttingToFit(cellFeatures, startRow, startColumn, endRow2, endColumn2);
		endRow2 = endOfArea2.getRow();
		endColumn2 = endOfArea2.getColumn();
		
		// Compare areas
		if  ( (endRow1 >= endRow2) && (endColumn1 >= endColumn2) ) {
			idMap.add( splitArea(sheet, cellFeatures, StructureType.LEGEND, id, startRow, startColumn, endRow1, endColumn1));
		} else if ( (endRow1 <= endRow2) && (endColumn1 <= endColumn2) ) { 
			idMap.add(splitArea(sheet, cellFeatures, StructureType.LEGEND, id, startRow, startColumn, endRow2, endColumn2));
		} else {
			idMap.add( splitArea(sheet, cellFeatures, StructureType.LEGEND, id, startRow, endColumn2+1, endRow1, endColumn1));
			idMap.add(splitArea(sheet, cellFeatures, StructureType.LEGEND, idMap.getMaxIndex()+1, endRow1+1, startColumn, endRow2, endColumn2));
			
			for (int index = startIndex; index <= idMap.getMaxIndex(); index++)
				idMap.addArea(new AreaInformation(StructureType.LEGEND, index, new RangeCoordinates(sheet, startRow, startColumn, endRow1, endColumn2)));			
		}
		return idMap;
	}
	
	private static AEResults extractFBArea(String sheet, CellAttributeInformation[][] cellFeatures, int id, int startRow, int startColumn,  FeatureMaps features ) {
		AEResults results = new AEResults(sheet, cellFeatures.length, cellFeatures[0].length);
		
		if (cellFeatures[startRow][startColumn].getCellType() != StructureType.FB)
			return results;
		
		// Expand area to the right and then to the bottom
		int endColumn = startColumn;
		while ( (endColumn+1 < cellFeatures[startRow].length) &&
				features.sameFeatures(startRow, startColumn, startRow, endColumn+1) &&
				( (cellFeatures[startRow][endColumn+1].getCellType() == StructureType.FB) || 
				  (cellFeatures[startRow][endColumn+1].getCellType() == StructureType.EMPTY) ) )
			endColumn++;
		
		// Now expand to the bottom
		int endRow = startRow;
		Boolean expand = true;
		while (expand && (endRow+1 < cellFeatures.length)) {
			Boolean allValid = true;

			for(int j = startColumn; j <= endColumn; j++) {
				if ( ( (cellFeatures[endRow+1][j].getCellType() !=StructureType.FB) && 
					   (cellFeatures[endRow+1][j].getCellType() !=StructureType.EMPTY) )  ||
					   !features.sameFeatures(startRow, startColumn, endRow+1, j ) )
					allValid = false;
			
			}
			if (allValid)
				endRow++;
			else
				expand = false;
		}
		
		CellSpaceInformation endOfArea = cuttingToFit(cellFeatures, startRow, startColumn, endRow, endColumn);
		endRow = endOfArea.getRow();
		endColumn = endOfArea.getColumn();
		
		results.addArea(new AreaInformation(StructureType.FB, id, new RangeCoordinates(sheet, startRow, startColumn, endRow, endColumn)) ) ;
		
		return results;
	}
	
	/**
	 * Marks a 2 dimensional map with ids whereby areas in the worksheet with the same celltype are mapped to the same id.
	 * @param sheet The actual worksheet.
	 * @param cellFeatures A 2 dimensional array of cell features.
	 * @param map The 2 dimensional map that should be marked.
	 */
	public static void markMapByCellType(Sheet sheet, CellAttributeInformation[][] cellFeatures, Integer[][] map) {
		Map<Integer, Integer> cellType2Id = new HashMap<Integer, Integer>();
		int maxId = 0;
		for (int row = 0; row < map.length; row++) {
			for (int column = 0; column < map[row].length; column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if (cell != null) {
					if (cellType2Id.containsKey(cellFeatures[row][column].getCellType().ordinal()) )
						map[row][column] = cellType2Id.get(cellFeatures[row][column].getCellType().ordinal());
					else {
						map[row][column] = maxId;
						cellType2Id.put(cellFeatures[row][column].getCellType().ordinal(), maxId);
						maxId++;
					}
						
				} else
					map[row][column] = -1;
			}
		}
		
	}
	
	/**
	 * Marks a 2 dimensional map with the id 0.
	 * @param sheet The actual worksheet.
	 * @param map The 2 dimensional map that should be marked.
	 */
	public static void markMapUniform(Sheet sheet, Integer[][] map) {
		for (int i = 0; i < map.length; i++)
			for (int j = 0; j < map[i].length; j++)
				map[i][j] = 0;
	}
	
	/**
	 * Marks a 2 dimensional map with ids whereby areas in the worksheet with the same color are mapped to the same id.
	 * @param sheet The actual worksheet.
	 * @param map The 2 dimensional map that should be marked.
	 */
	public static void markMapByColor(Sheet sheet, Integer[][] map) {
		Map<Integer, Integer> color2Id = new HashMap<Integer, Integer>();
		int maxId = 0;
		for (int row = 0; row < map.length; row++) {
			for (int column = 0; column < map[row].length; column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if (cell != null) {
					if (color2Id.containsKey(cell.getBackgroundColor()) )
						map[row][column] = color2Id.get(cell.getBackgroundColor());
					else {
						map[row][column] = maxId;
						color2Id.put(cell.getBackgroundColor(), maxId);
						maxId++;
					}
						
				} else
					map[row][column] = -1;
			}
		}

	}
	
	/**
	 * Marks a 2 dimensional map with ids whereby areas in the worksheet with the same font are mapped to the same id.
	 * @param sheet The actual worksheet.
	 * @param map The 2 dimensional map that should be marked.
	 */
	public static void markMapByFont(Sheet sheet, Integer[][] map) {
		Map<Font, Integer> font2Id = new HashMap<Font, Integer>();
		int maxId = 0;
		for (int row = 0; row < map.length; row++) {
			for (int column = 0; column < map[row].length; column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if ((cell != null) && (cell.getFont() != null)) {
					if (font2Id.containsKey(cell.getFont()) )
						map[row][column] = font2Id.get(cell.getFont());
					else {
						map[row][column] = maxId;
						font2Id.put(cell.getFont(), maxId);
						maxId++;
					}
						
				} else
					map[row][column] = -1;
			}
		}
		
	}
	
	/**
	 * Marks a 2 dimensional map with ids whereby areas in the worksheet with the same formula are mapped to the same id.
	 * @param sheet The actual worksheet.
	 * @param map The 2 dimensional map that should be marked.
	 * @param cellFormulae Contains the cell formula for formulae of a worksheet.
	 */
	public static void markMapByFormulae(Sheet sheet, Integer[][] map, Map<CellSpaceInformation, psf.ParserResult> cellFormulae) {
		Map<String, Integer> formula2Id = new HashMap<String, Integer>();
		int maxId = 0;
		for (int row = 0; row < map.length; row++) {
			for (int column = 0; column < map[row].length; column++) {
				Cell cell = sheet.getCellForPosition(row, column);
				if ((cell != null) && (!cell.getFormula().isEmpty())) {
					String unifiedFormula = cellFormulae.get(new CellSpaceInformation(sheet.getId(), row, column)).getMathML();
					if (formula2Id.containsKey(unifiedFormula) )
						map[row][column] = formula2Id.get(unifiedFormula);
					else {
						map[row][column] = maxId;
						formula2Id.put(unifiedFormula, maxId);
						maxId++;
					}
						
				} else
					map[row][column] = -1;
			}
		}

	}
	
	/**
	 * Marks a 2 dimensional map with ids whereby areas in the worksheet within the same border are mapped to the same id.
	 * @param sheet The actual worksheet.
	 * @param map The 2 dimensional map that should be marked.
	 */
	public static void markMapByBorder(Sheet sheet, Integer[][] map) {
		int index = 0;
		int row = 0;
		while (row < sheet.getMaxRow()) {
			int column = getNextElementInRow(sheet, row, -1, false);
			while (column < sheet.getMaxColumn()) {
				int previousElementIndex = getPreviousElementInRow(sheet, row, column, false);
				int upperElementIndex = getPreviousElementInColumn(sheet, row, column, false);
				if ( (previousElementIndex >= 0) && 
						sheet.getCellForPosition(row, column).getBorder().getLeft().isSmallerOrEqualThen(sheet.getCellForPosition(row, column).getBorder().getRight()))
					markArea(row, previousElementIndex, row, column, map, map[row][previousElementIndex]);
				else if ( (upperElementIndex >= 0) && 
						sheet.getCellForPosition(row, column).getBorder().getTop().isSmallerOrEqualThen(sheet.getCellForPosition(row, column).getBorder().getBottom()))
					markArea(upperElementIndex, column, row, column, map, map[upperElementIndex][column]);
				else {
					index++;
					map[row][column] = new Integer(index);
				}
				column = getNextElementInRow(sheet, row, column, false);
			}
			row++;
		}
		//eliminateNull(map);
	}
	
	
	private static int getPreviousElementInRow(Sheet sheet, int row, int column, Boolean ignoreEmpty) {
		Boolean found = false;
		column--;
		while (!found && (column >= 0) && (sheet.getCellForPosition(row, column) != null)) {
			Cell cell = sheet.getCellForPosition(row, column);
			if (!cell.isHidden() && (!cell.getContent().isEmpty() || !ignoreEmpty) )
				found = true;
			else
				column--;
		}
		return column;
	}
	
	private static int getNextElementInRow(Sheet sheet, int row, int column, Boolean ignoreEmpty) {
		Boolean found = false;
		column++;
		while (!found && (column < sheet.getMaxColumn()) ) {
			Cell cell = sheet.getCellForPosition(row, column);
			if (!cell.isHidden() && (!cell.getContent().isEmpty() || !ignoreEmpty) )
				found = true;
			else
				column++;
		}
		return column;
	}
	
	private static int getPreviousElementInColumn(Sheet sheet, int row, int column, Boolean ignoreEmpty) {
		Boolean found = false;
		row--;
		while (!found && (row >= 0)) {
			Cell cell = sheet.getCellForPosition(row, column);
			if (!cell.isHidden() && (!cell.getContent().isEmpty() || !ignoreEmpty) )
				found = true;
			else
				row--;
		}
		return row;
	}
	
	private static void markArea(int startRow, int startColumn, int endRow, int endColumn, Integer[][] map, int value) {
		for (int row = startRow; row <= endRow; row++)
			for (int column = startColumn; column <= endColumn; column++)
				map[row][column] = new Integer(value);
	}

	
	private static CellSpaceInformation cuttingToFit(CellAttributeInformation[][] sheet, int startRow, int startColumn, int endRow, int endColumn) {
		Boolean stop = false;
		while (!stop) {
			for (int row = startRow; row <= endRow; row++) {
				if (sheet[row][endColumn].getCellType() != StructureType.EMPTY)
					stop = true;
			}
			if (!stop)
				endColumn--;
		}
		stop = false;
		while (!stop) {
			for (int column = startColumn; column <= endColumn; column++) {
				if (sheet[endRow][column].getCellType() != StructureType.EMPTY)
					stop = true;
			}
			if (!stop)
				endRow--;
		}
		
		return new CellSpaceInformation(endRow, endColumn);
	}
	
	private static AEResults splitArea(String sheetName, CellAttributeInformation[][] sheet, StructureType type, int id, int startRow, int startColumn, int endRow, int endColumn) {
		AEResults areas = new AEResults(sheetName, sheet.length, sheet[0].length);
		
		if ((startRow == endRow) || (startColumn == endColumn)) 
			areas.addArea(new AreaInformation(type, id, new RangeCoordinates(sheetName, startRow, startColumn, endRow, endColumn) ) );
		else if ((endColumn - startColumn > endRow - startRow) && CellAttributeInformationUtil.aboveFB(sheet, startRow, startColumn) ) {
			for (int row = startRow; row <= endRow; row++, id++)
				areas.addArea(new AreaInformation(type, id, new RangeCoordinates(sheetName, row, startColumn, row, endColumn) ));
		} else if ((endRow - startRow > endColumn - startColumn) && CellAttributeInformationUtil.besideFB(sheet, startRow, startColumn) ) {
			for (int column = startColumn; column <= endColumn; column++, id++)
				areas.addArea(new AreaInformation(type, id, new RangeCoordinates(sheetName, startRow, endRow, column, column) ));
		} else 
			areas.addArea(new AreaInformation(type, id, new RangeCoordinates(sheetName, startRow, startColumn, endRow, endColumn) ));
		
		return areas;
	}
	
}
