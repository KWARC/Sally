package info.kwarc.sally.spreadsheet3.extraction;

import static org.junit.Assert.*;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.CellStyle;
import org.apache.poi.ss.usermodel.Font;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.ss.usermodel.WorkbookFactory;
import org.apache.poi.ss.util.CellRangeAddress;
import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;




import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.extraction.BorderLine;
import info.kwarc.sally.spreadsheet3.extraction.BorderLine.ExcelBorderStyle;
import info.kwarc.sally.spreadsheet3.extraction.BorderLine.ExcelBorderWeight;
import info.kwarc.sally.spreadsheet3.extraction.BorderLine.FormatStyle;


public class ExtractionInterfaceTest {
	ExtractionInterface extractor;
	Workbook workbook = null;
	
	final String workbookFilename = System.getProperty("user.dir") + "\\src\\test\\resources\\info\\kwarc\\sally\\spreadsheet3\\extraction\\Example1.xls";
	
	final static Logger logger = LoggerFactory.getLogger(ExtractionInterfaceTest.class);
	
	@Before
	public void setUp() throws Exception {
		extractor = new ExtractionInterface();
		workbook = WorkbookFactory.create(new FileInputStream(workbookFilename));
	}

	@Test
	public void testExtractStructures() throws FileNotFoundException {
		List<info.kwarc.sally.spreadsheet3.extraction.Sheet> sheets = parseSpreadsheet(workbook,10000);
		ParsingResult results = extractor.extractStructures(sheets, new ExtractionParameter(true, true, true, true, true, true));
		assertTrue(results.getAeResults().size() == 1);
		assertTrue(results.getAeResults().get(0).getAreas().size() == 14);
		assertTrue(results.getAeResults().get(0).getAreas().get(4).getStartRow() == 4 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(4).getEndRow() == 4 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(4).getStartColumn() == 0 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(4).getEndColumn() == 0 ); 
		
		assertTrue(results.getAeResults().get(0).getAreas().get(5).getStartRow() == 4 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(5).getEndRow() == 4 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(5).getStartColumn() == 1 ); 
		assertTrue(results.getAeResults().get(0).getAreas().get(5).getEndColumn() == 5 ); 
		
		assertTrue(results.getAffInfos().size() == 5);
		assertTrue(results.getAffInfos().get(0).getId() == 5);
		assertTrue(results.getAffInfos().get(0).getAffiliatedIds().size() == 4);
		assertTrue(results.getAffInfos().get(0).getAffiliatedIds().contains(3));
		assertTrue(results.getAffInfos().get(0).getAffiliatedIds().contains(2));
		assertTrue(results.getAffInfos().get(0).getAffiliatedIds().contains(1));
		assertTrue(results.getAffInfos().get(0).getAffiliatedIds().contains(4));
		/*for (AEResults r : results.getAeResults())
			System.out.println(r.toString());
		for (AffiliationInformation i : results.getAffInfos())
			System.out.println(i.toString());*/
	}
	
	static public List<info.kwarc.sally.spreadsheet3.extraction.Sheet> parseSpreadsheet(Workbook wb, int maxRows) {
		List<info.kwarc.sally.spreadsheet3.extraction.Sheet> sheets = new ArrayList<info.kwarc.sally.spreadsheet3.extraction.Sheet>();
		
		for (int i = 0; i < wb.getNumberOfSheets(); i++) {
			Sheet s = wb.getSheetAt(i);
			if ((maxRows == 0) || (s.getLastRowNum() <= maxRows))
				sheets.add(convertSheet(wb, s));
			else
				logger.info("Skipping spreadsheet " + s.getSheetName() + " with " + s.getLastRowNum() + " rows.");
		}

		return sheets;
	}
	
	static private info.kwarc.sally.spreadsheet3.extraction.Sheet convertSheet(Workbook wb, Sheet sheet) {
		// Search merged regions
		Map<CellSpaceInformation, CellSpaceInformation> mergedCells = new HashMap<CellSpaceInformation, CellSpaceInformation>();
		for (int i = 0; i < sheet.getNumMergedRegions(); i++) {
			CellRangeAddress range = sheet.getMergedRegion(i);
			CellSpaceInformation start = new CellSpaceInformation(sheet.getSheetName(), range.getFirstRow(), range.getFirstColumn());
			CellSpaceInformation end = new CellSpaceInformation(sheet.getSheetName(), range.getLastRow(), range.getLastColumn());
			mergedCells.put(start, end);
		}

		// Convert all cells
		info.kwarc.sally.spreadsheet3.extraction.Sheet sheetRep = new info.kwarc.sally.spreadsheet3.extraction.Sheet(sheet.getSheetName());
		int maxColumn = 0;

		for (int row = 0; row <= sheet.getLastRowNum(); row++) {
			Row rowComplete = sheet.getRow(row);
			if (rowComplete != null) {
				maxColumn = Math.max(maxColumn, rowComplete.getLastCellNum());
				for (int column = 0; column <= rowComplete.getLastCellNum(); column++) {
					Cell cell = rowComplete.getCell(column);
					if (cell != null)
						sheetRep.addCell(convertCell(wb, cell, mergedCells));
				}
			}
		}

		// Add cell entries for empty cells
		for (int row = 0; row < sheetRep.getMaxRow(); row++) {
			for (int column = 0; column < sheetRep.getMaxColumn(); column++) {
				if (sheetRep.getCellForPosition(row, column) == null)
					sheetRep.addCell(createEmptyCell(sheet.getSheetName(), row, column));
			}
		}

		return sheetRep;
	}

	private static info.kwarc.sally.spreadsheet3.extraction.Cell createEmptyCell(
			String sheetName, int row, int column) {
		CellSpaceInformation position = new CellSpaceInformation(sheetName, row, column);
		info.kwarc.sally.spreadsheet3.extraction.Font font = new info.kwarc.sally.spreadsheet3.extraction.Font("", 0, 0.0f, false, (short)0, (short)0);
		info.kwarc.sally.spreadsheet3.extraction.BorderLine borderLine = new info.kwarc.sally.spreadsheet3.extraction.BorderLine(0, FormatStyle.EXCELSTYLE, ExcelBorderStyle.NONE, ExcelBorderWeight.HAIRLINE);
		info.kwarc.sally.spreadsheet3.extraction.CellBorder cellBorder = new info.kwarc.sally.spreadsheet3.extraction.CellBorder(borderLine,borderLine,borderLine,borderLine);
		
		return new info.kwarc.sally.spreadsheet3.extraction.Cell(position, "", "", 0, font, cellBorder);
	}

	static private info.kwarc.sally.spreadsheet3.extraction.Cell convertCell(Workbook wb, Cell cell, Map<CellSpaceInformation, CellSpaceInformation> mergedCells) {
		CellSpaceInformation position = new CellSpaceInformation(cell.getSheet().getSheetName(),
				cell.getRowIndex(), cell.getColumnIndex());
		
		if (mergedCells.containsKey(position)) {
			CellSpaceInformation posEnd = mergedCells.get(position);
			int heigth = posEnd.getRow() - position.getRow() + 1;
			int width = posEnd.getColumn() - position.getColumn() + 1;
			position = new CellSpaceInformation(position.getWorksheet(), position.getRow(), position.getColumn(), heigth, width);
		}
		
		CellTypeContent c = Util.getCellContent(cell);
		String value = "";
		String formula = "";
		if (c != null) {
			value = c.getContent();
			formula = c.getFormula();
		}
		int backgroundColor = cell.getCellStyle().getFillForegroundColor();
		//cell.getCellStyle().
		info.kwarc.sally.spreadsheet3.extraction.Font font = convertFont(wb.getFontAt(cell.getCellStyle().getFontIndex()));
		CellBorder border = convertBorder(cell);
		
		return new info.kwarc.sally.spreadsheet3.extraction.Cell(position, value, formula, backgroundColor, font, border);
	}
	
	static private info.kwarc.sally.spreadsheet3.extraction.Font convertFont(Font font) {
		return new info.kwarc.sally.spreadsheet3.extraction.Font(font.getFontName(), font.getColor(), font.getFontHeight(), font.getItalic(), 
				font.getBoldweight(), font.getUnderline());
		
	}
	
	static private CellBorder convertBorder(Cell cell) {
		CellStyle style = cell.getCellStyle();
		return new CellBorder(convertBorderLine(style.getBorderTop(), style.getTopBorderColor()), 
				convertBorderLine(style.getBorderBottom(), style.getBottomBorderColor()),
				convertBorderLine(style.getBorderLeft(), style.getLeftBorderColor()),
				convertBorderLine(style.getBorderRight(), style.getRightBorderColor()) );
	}
	
	static private BorderLine convertBorderLine(short borderLine, short borderColor) {
		switch (borderLine) {
		case CellStyle.BORDER_NONE:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.NONE, ExcelBorderWeight.HAIRLINE);
		case CellStyle.BORDER_HAIR:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.CONTINUOUS, ExcelBorderWeight.HAIRLINE);
		case CellStyle.BORDER_DOTTED:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DOT, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_DASH_DOT_DOT:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH_DOT_DOT, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_DASH_DOT:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH_DOT, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_DASHED:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_THIN:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.CONTINUOUS, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_DOUBLE:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DOUBLE, ExcelBorderWeight.THIN);
		case CellStyle.BORDER_MEDIUM_DASH_DOT_DOT:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH_DOT_DOT, ExcelBorderWeight.MEDIUM);
		case CellStyle.BORDER_MEDIUM_DASH_DOT:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH_DOT, ExcelBorderWeight.MEDIUM);
		case CellStyle.BORDER_MEDIUM_DASHED:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.DASH, ExcelBorderWeight.MEDIUM);
		case CellStyle.BORDER_SLANTED_DASH_DOT:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.SLANT_DASH_DOT, ExcelBorderWeight.MEDIUM);
		case CellStyle.BORDER_MEDIUM:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.CONTINUOUS, ExcelBorderWeight.MEDIUM);
		case CellStyle.BORDER_THICK:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.CONTINUOUS, ExcelBorderWeight.THICK);
		default:
			return new BorderLine(borderColor, FormatStyle.EXCELSTYLE, ExcelBorderStyle.NONE, ExcelBorderWeight.HAIRLINE);
		}
	}

}
