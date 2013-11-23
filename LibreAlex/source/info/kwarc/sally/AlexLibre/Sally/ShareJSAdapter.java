package info.kwarc.sally.AlexLibre.Sally;

import info.kwarc.sally.sharejs.JSONSnapshot;
import info.kwarc.sally.sharejs.ShareJS;
import info.kwarc.sally.sharejs.models.SpreadsheetModel;
import info.kwarc.sally.sharejs.models.SpreadsheetModel.Cell;
import info.kwarc.sally.sharejs.models.SpreadsheetModel.Sheet;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.sun.star.container.XIndexAccess;
import com.sun.star.sheet.XCellRangeAddressable;
import com.sun.star.sheet.XSheetCellCursor;
import com.sun.star.sheet.XSpreadsheet;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.sheet.XSpreadsheets;
import com.sun.star.sheet.XUsedAreaCursor;
import com.sun.star.table.XCellRange;
import com.sun.star.uno.UnoRuntime;

public class ShareJSAdapter {
	String url;
	ShareJS sharejs;
	Logger log;
	ObjectMapper mapper; 
	static final String collection = "libreoffice";
	

	public ShareJSAdapter(String url) {
		this.url = url;
		sharejs = new ShareJS(url);
		log = LoggerFactory.getLogger(getClass());
		mapper = new ObjectMapper();
		
	}

	/**
	 * Analyzes all the cells in a sheet.
	 * 
	 * @param xSpreadsheet
	 *            - The sheet to be analyzed
	 * @return - sally.Sheet object containning data for all the cells in the
	 *         sheet and other additional information. Returns null in case of
	 *         failure.
	 */
	public void getSheetData(XSpreadsheet xSpreadsheet, Sheet s) { 
		int startRow, startCol, endRow, endCol;

		try { 

			/*
				This code is used to get the used area of a Spreadsheet, it takes into
				account formatting, content in principle everything.
			 */

			XSheetCellCursor xSheetCellCursor = xSpreadsheet.createCursor();
			XUsedAreaCursor xUsedAreaCursor = (XUsedAreaCursor) UnoRuntime.queryInterface(XUsedAreaCursor.class, xSheetCellCursor);
			xUsedAreaCursor.gotoStartOfUsedArea(false);
			xUsedAreaCursor.gotoEndOfUsedArea(true);

			XCellRange xCellRange = (XCellRange) UnoRuntime.queryInterface( XCellRange.class, xUsedAreaCursor);
			XCellRangeAddressable cellrange = (XCellRangeAddressable) UnoRuntime.queryInterface(XCellRangeAddressable.class, xCellRange);
			startRow =	cellrange.getRangeAddress().StartRow;
			startCol = cellrange.getRangeAddress().StartColumn;
			endRow = cellrange.getRangeAddress().EndRow;
			endCol = cellrange.getRangeAddress().EndColumn;

			for (int row = startRow; row < endRow;row++) 
				for (int col = startCol; col < endCol; col++) { 
					String formula = SCUtil.getFormulaFromCell(xSpreadsheet, col, row);
					if (formula.length() == 0)
						continue;
					s.setContent(row, col, new Cell().setFormula(formula).setValue(Double.toString(SCUtil.getValueFromCell(xSpreadsheet, col, row))));					
				}
		} catch (Exception e) { 
			log.debug("getSheetData" + e);
		} 
	}

	/**
	 * This function analyzes a document sheet by sheet.
	 * 
	 * @param xSpreadsheetDocument
	 *            - The document to analyze
	 */
	public void analyzeDocument(XSpreadsheetDocument xSpreadsheetDocument, SpreadsheetModel model) {
		XSpreadsheets sheets = xSpreadsheetDocument.getSheets();
		List<Sheet> myList = new ArrayList<Sheet>();
		XIndexAccess xSheetsIndexAccess = UnoRuntime.queryInterface(
				XIndexAccess.class, sheets);
		try {
			for (int i = 0; i < xSheetsIndexAccess.getCount(); i++) {
				Object op = xSheetsIndexAccess.getByIndex(i);
				XSpreadsheet xSpreadsheet = (XSpreadsheet) UnoRuntime.queryInterface(XSpreadsheet.class, op);
				String sheetName = SCUtil.getSCSheetNameByIndex(xSpreadsheetDocument, (short) i);
				Sheet s = model.addSheet(sheetName);
				getSheetData(xSpreadsheet, s);
			}
		} catch (Exception e) {
			log.debug("analyzeDocument" + e);
		}
	}

	public void exportSpreadsheet(XSpreadsheetDocument xSpreadsheetDocument) {
		String path = SallyUtils.getDocumentName(xSpreadsheetDocument);
		if (sharejs.existFile(collection, path)) {
			sharejs.deleteFile(collection, path);
		}
		SpreadsheetModel model = new SpreadsheetModel();
		analyzeDocument(xSpreadsheetDocument, model);

		String json;
		try {
			json = mapper.writeValueAsString(model);
			JSONSnapshot.create(sharejs, collection, path, json);			
		} catch (JsonProcessingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
