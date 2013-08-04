package info.kwarc.sally.AlexLibre.Sally;

import info.kwarc.sally.AlexLibre.LibreAlex.LibreSelectionChange;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexData;

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

		xSelectionSupplier.addSelectionChangeListener(new LibreSelectionChange(xSpreadsheetDocument));
	}
	
	void init() {
		startSelectionListen(xSpreadsheetDocument);
		getSemanticData();
	}
	
	public SpreadsheetDoc(XSpreadsheetDocument xSpreadsheetDocument) {
		this.xSpreadsheetDocument = xSpreadsheetDocument;
		log = LoggerFactory.getLogger(getClass());
		init();
	}
	
	public AlexData getSemanticData() {
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
