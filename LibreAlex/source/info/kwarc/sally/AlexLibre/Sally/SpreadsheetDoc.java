package info.kwarc.sally.AlexLibre.Sally;

import info.kwarc.sally.AlexLibre.LibreAlex.LibreSelectionChange;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexData;
import sally.RangeSelection;

import com.sun.star.lang.XMultiServiceFactory;
import com.sun.star.sheet.XSheetCellRangeContainer;
import com.sun.star.sheet.XSpreadsheet;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.sheet.XSpreadsheetView;
import com.sun.star.table.XCell;
import com.sun.star.uno.UnoRuntime;
import com.sun.star.view.XSelectionSupplier;

public class SpreadsheetDoc {
	XSpreadsheetDocument xSpreadsheetDocument;
	Logger log;
	static final String hidenSheetName = "sally";
	SallyCommunication comm;

	public int getIndexOfSpreadsheet(String sheetName)
			throws com.sun.star.uno.Exception {
		XSpreadsheetDocument doc = xSpreadsheetDocument;
		String[] nameVector = doc.getSheets().getElementNames();
		for (int i = 0; i < nameVector.length; i++)
			if (sheetName.toLowerCase().contentEquals(
					nameVector[i].toLowerCase()))
				return i;
		throw new com.sun.star.uno.Exception(
				"Spreadsheet is not part of the current workbook\n");
	}

	private void insertRange(
			com.sun.star.sheet.XSheetCellRangeContainer xContainer, int nSheet,
			int nStartCol, int nStartRow, int nEndCol, int nEndRow,
			boolean bMerge) throws RuntimeException, Exception {
		com.sun.star.table.CellRangeAddress aAddress = new com.sun.star.table.CellRangeAddress();
		aAddress.Sheet = (short) nSheet;
		aAddress.StartColumn = nStartCol;
		aAddress.StartRow = nStartRow;
		aAddress.EndColumn = nEndCol;
		aAddress.EndRow = nEndRow;
		xContainer.addRangeAddress(aAddress, bMerge);
	}

	/**
	 * Add selection change listener for a spreadsheet program
	 * @param xSpreadsheetDocument
	 */
	public void startSelectionListen(XSpreadsheetDocument xSpreadsheetDocument) {
		com.sun.star.frame.XModel xModel = (com.sun.star.frame.XModel) UnoRuntime
				.queryInterface(com.sun.star.frame.XModel.class,
						xSpreadsheetDocument);

		XSpreadsheetView xSheetView = (XSpreadsheetView) UnoRuntime
				.queryInterface(XSpreadsheetView.class,
						xModel.getCurrentController());
		XSelectionSupplier xSelectionSupplier = (XSelectionSupplier) UnoRuntime
				.queryInterface(XSelectionSupplier.class,
						xSheetView);

		xSelectionSupplier.addSelectionChangeListener(new LibreSelectionChange(xSpreadsheetDocument, comm));
	}

	public void selectRange(List<RangeSelection> ranges) {
		try {

			com.sun.star.frame.XModel xModel = (com.sun.star.frame.XModel) UnoRuntime
					.queryInterface(com.sun.star.frame.XModel.class,
							xSpreadsheetDocument);

			XSpreadsheetView xSheetView = (XSpreadsheetView) UnoRuntime
					.queryInterface(XSpreadsheetView.class,
							xModel.getCurrentController());

			XSelectionSupplier xSelectionSupplier = (XSelectionSupplier) UnoRuntime
					.queryInterface(XSelectionSupplier.class, xSheetView);

			XMultiServiceFactory xDocFactory = (XMultiServiceFactory) UnoRuntime
					.queryInterface(
							com.sun.star.lang.XMultiServiceFactory.class,
							xModel);
			XSheetCellRangeContainer xRangeCont = (XSheetCellRangeContainer) UnoRuntime
					.queryInterface(
							com.sun.star.sheet.XSheetCellRangeContainer.class,
							xDocFactory
							.createInstance("com.sun.star.sheet.SheetCellRanges"));


			for (int i = 0; i < ranges.size(); i++) {
				RangeSelection el = ranges.get(i);
				insertRange(xRangeCont, getIndexOfSpreadsheet(el.getSheet()), el.getStartCol(),
						el.getStartRow(), el.getEndCol(), el.getEndRow(),
						false);
			}
			xSelectionSupplier.select(xRangeCont);
		} catch (Exception e) {

		}
	}

	void init() {
		startSelectionListen(xSpreadsheetDocument);
		comm.sendMessage("/service/alex/semanticdata", getSemanticData());
	}

	public SpreadsheetDoc(XSpreadsheetDocument xSpreadsheetDocument, SallyCommunication comm) {
		this.xSpreadsheetDocument = xSpreadsheetDocument;
		this.comm = comm;
		log = LoggerFactory.getLogger(getClass());
		init();
	}

	public AlexData getSemanticData() {
		AlexData.Builder alexData = AlexData.newBuilder();
		alexData.setData("");
		alexData.setFileName("new_document");
		try {
			Object op = xSpreadsheetDocument.getSheets().getByName(hidenSheetName);
			XSpreadsheet xSpreadsheet = (XSpreadsheet) UnoRuntime
					.queryInterface(XSpreadsheet.class, op);

			alexData.setFileName(SallyUtils.getDocumentName(xSpreadsheetDocument));
			int row = 0;
			String data = "";
			XCell xCell;
			do {
				xCell = xSpreadsheet.getCellByPosition(0, row++);
				data += xCell.getFormula();
			} while (xCell.getFormula().length()>0);
			alexData.setData(data);
		} catch (Exception e) {
			e.printStackTrace();
		}
		return alexData.build();
	}

	public void setSemanticData(AlexData data) {
		AlexData.Builder alexData = AlexData.newBuilder();
		alexData.setData("");
		alexData.setFileName("new_document");
		try {
			Object op = xSpreadsheetDocument.getSheets().getByName(hidenSheetName);
			log.info("hidden sheet = "+op);
			XSpreadsheet xSpreadsheet = (XSpreadsheet) UnoRuntime
					.queryInterface(XSpreadsheet.class, op);

			alexData.setFileName(SallyUtils.getDocumentName(xSpreadsheetDocument));
			XCell xCell = xSpreadsheet.getCellByPosition(0, 0);
			alexData.setData(xCell.getFormula());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
