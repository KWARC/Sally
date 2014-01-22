package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.ContentValueType;


public class CellAttributeInformationUtil {
	
	public static Boolean hasAssocLegends(CellAttributeInformation[][] cellInformation, int row, int column) {
		Boolean assocLegendAbove = false;
		Boolean assocLegendLeft = false;
		for (int i=0; i < row; i++)
			if (cellInformation[i][column].getCellType() == StructureType.LEGEND)
				assocLegendAbove = true;
		for (int j = 0; j < column; j++)
			if (cellInformation[row][j].getCellType() == StructureType.LEGEND)
				assocLegendLeft = true;
		return (assocLegendAbove && assocLegendLeft);
	}
	
	public static Boolean hasAssocFB(CellAttributeInformation[][] cellInformation, int row, int column) {
		return (aboveFB(cellInformation,row,column) || besideFB(cellInformation,row,column) );
	}
	
	public static Boolean aboveFB(CellAttributeInformation[][] cellInformation, int row, int column) {
		Boolean assocFBBelow = false;
		for (int i=row+1; i < cellInformation.length; i++)
			if (cellInformation[i][column].getCellType() == StructureType.FB)
				assocFBBelow = true;
		return assocFBBelow;
	}
	
	public static Boolean besideFB(CellAttributeInformation[][] cellInformation, int row, int column) {
		Boolean assocFBRight = false;
		for (int j = column+1; j < cellInformation[row].length; j++)
			if (cellInformation[row][j].getCellType() == StructureType.FB)
				assocFBRight = true;
		return assocFBRight;
	}
	
	public static CellAttributeInformation createAttributes(Sheet sheet, int row, int column, CellAttributeInformation[][] cellInformation) {
		Cell cell = sheet.getCellForPosition(row, column);		
		
		Boolean leftBorder = ((column==0) || sheet.getCellForPosition(row, column-1).getContent().isEmpty()  );
		Boolean upperBorder = ((row==0) || sheet.getCellForPosition(row-1, column).getContent().isEmpty() );
		
		Boolean assocLegends = CellAttributeInformationUtil.hasAssocLegends(cellInformation, row, column);
		Boolean isBold = cell.getFont().IsBold();
		Boolean isItalic = cell.getFont().IsItalic();
		Boolean isUnderlined = cell.getFont().IsUnderlined();
			
		StructureType leftType = (column==0) ? StructureType.EMPTY : cellInformation[row][column-1].getCellType(); 
		StructureType upperType = (row==0) ? StructureType.EMPTY : cellInformation[row-1][column].getCellType();
		
		ContentValueType contentType = Util.identifyValueType(cell.getContent());
		
		return new CellAttributeInformation(leftBorder, upperBorder, assocLegends, isBold, isItalic, isUnderlined,
				leftType, upperType, contentType);
	}
	
	public static CellAttributeInformation createLocalAttributes(Sheet sheet, int row, int column, StructureType type) {
		Cell cell = sheet.getCellForPosition(row, column);
		Boolean leftBorder = ((column==0) || (sheet.getCellForPosition(row, column-1) == null) || sheet.getCellForPosition(row, column-1).getContent().isEmpty()  );
		Boolean upperBorder = ((row==0) || (sheet.getCellForPosition(row-1, column) == null) || sheet.getCellForPosition(row-1, column).getContent().isEmpty() );
		ContentValueType contentType = ContentValueType.EMPTY;
		Boolean isBold = false;
		Boolean isItalic = false;
		Boolean isUnderlined = false;
		
		if (cell != null) {
			contentType = Util.identifyValueType(cell.getContent());
			isBold = cell.getFont().IsBold();
			isItalic = cell.getFont().IsItalic();
			isUnderlined = cell.getFont().IsUnderlined();
		}
		
		return new CellAttributeInformation(type, leftBorder, upperBorder, isBold, isItalic, isUnderlined, contentType);
	}
}
