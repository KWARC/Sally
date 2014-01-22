package info.kwarc.sally.AlexLibre.Sally;

/**************************************************************
 * 
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 * 
 *   http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 * 
 *************************************************************/


import java.util.HashMap;

import com.sun.star.awt.Rectangle;
import com.sun.star.beans.XPropertySet;
import com.sun.star.chart.XChartDocument;
import com.sun.star.chart.XDiagram;
import com.sun.star.container.XIndexAccess;
import com.sun.star.container.XNameAccess;
import com.sun.star.container.XNamed;
import com.sun.star.document.XEmbeddedObjectSupplier;
import com.sun.star.frame.XController;
import com.sun.star.frame.XModel;
import com.sun.star.frame.XStorable;
import com.sun.star.lang.XComponent;
import com.sun.star.lang.XMultiServiceFactory;
import com.sun.star.sheet.XCellRangeAddressable;
import com.sun.star.sheet.XSpreadsheet;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.sheet.XSpreadsheetView;
import com.sun.star.sheet.XSpreadsheets;
import com.sun.star.table.CellRangeAddress;
import com.sun.star.table.XCell;
import com.sun.star.table.XCellRange;
import com.sun.star.table.XColumnRowRange;
import com.sun.star.table.XTableChart;
import com.sun.star.table.XTableCharts;
import com.sun.star.table.XTableChartsSupplier;
import com.sun.star.table.XTableColumns;
import com.sun.star.table.XTableRows;
import com.sun.star.text.XText;
import com.sun.star.uno.UnoRuntime;
import com.sun.star.util.XCloseable;


/**
 * Utilities of Spreadsheet
 *
 */

public class SCUtil {
	
	private static final String scTempDir = "output/sc/"; //Spreadsheet temp file directory
	private static HashMap filterName = new HashMap(); 
		
	private SCUtil() {
		
	}
	
	/**
	 * Get spreadsheet document object
	 * @param xSpreadsheetComponent
	 * @return
	 * @throws Exception
	 */
    public static XSpreadsheetDocument getSCDocument(XComponent xSpreadsheetComponent) throws Exception {
    	XSpreadsheetDocument xSpreadsheetDocument = 
        		(XSpreadsheetDocument) UnoRuntime.queryInterface(XSpreadsheetDocument.class, xSpreadsheetComponent);
        
        return xSpreadsheetDocument;
    }
	
    /**
     * Get sheet object by sheet name
     * @param xSpreadsheetDocument
     * @param sheetName 
     * @return
     * @throws Exception
     */
	public static XSpreadsheet getSCSheetByName(XSpreadsheetDocument xSpreadsheetDocument, String sheetName) throws Exception {
		XSpreadsheets xSpreadsheets = xSpreadsheetDocument.getSheets();
		XSpreadsheet xSpreadsheet = 
				(XSpreadsheet) UnoRuntime.queryInterface(XSpreadsheet.class, xSpreadsheets.getByName(sheetName));
		
		return xSpreadsheet;
	}
	
	/**
	 * Get sheet object by sheet index
	 * @param xSpreadsheetDocument
	 * @param index   (Short) 0,1,2,...
	 * @return
	 * @throws Exception
	 */
	public static XSpreadsheet getSCSheetByIndex(XSpreadsheetDocument xSpreadsheetDocument, short index) throws Exception {
		XSpreadsheets xSpreadsheets = xSpreadsheetDocument.getSheets();
		XIndexAccess xIndexAccess = 
				(XIndexAccess) UnoRuntime.queryInterface(XIndexAccess.class, xSpreadsheets);
		XSpreadsheet xSpreadsheet = 
				(XSpreadsheet) UnoRuntime.queryInterface(XSpreadsheet.class, xIndexAccess.getByIndex(index));
		
		return xSpreadsheet;
	}
	
	/**
	 * Get sheet name by sheet index
	 * 
	 * @param xSpreadsheetDocument
	 * @param index
	 *            (Short) 0,1,2,...
	 * @return
	 * @throws Exception
	 */
	public static String getSCSheetNameByIndex(
			XSpreadsheetDocument xSpreadsheetDocument, short index)
			throws Exception {
		XSpreadsheets xSpreadsheets = xSpreadsheetDocument.getSheets();
		XIndexAccess xIndexAccess = (XIndexAccess) UnoRuntime.queryInterface(
				XIndexAccess.class, xSpreadsheets);
		XSpreadsheet xSpreadsheet = (XSpreadsheet) UnoRuntime.queryInterface(
				XSpreadsheet.class, xIndexAccess.getByIndex(index));
		XNamed xsheetname = (XNamed) UnoRuntime.queryInterface(XNamed.class,
				xSpreadsheet);
		return xsheetname.getName();
	}

	/**
	 * Set sheet name by sheet index
	 * 
	 * @param xSpreadsheetDocument
	 * @param index
	 *            (Short) 0,1,2,...
	 * @return
	 * @throws Exception
	 */
	public static void setSCSheetNameByIndex(
			XSpreadsheetDocument xSpreadsheetDocument, short index,
			String sheetname) throws Exception {
		XSpreadsheets xSpreadsheets = xSpreadsheetDocument.getSheets();
		XIndexAccess xIndexAccess = (XIndexAccess) UnoRuntime.queryInterface(
				XIndexAccess.class, xSpreadsheets);
		XSpreadsheet xSpreadsheet = (XSpreadsheet) UnoRuntime.queryInterface(
				XSpreadsheet.class, xIndexAccess.getByIndex(index));
		XNamed xsheetname = (XNamed) UnoRuntime.queryInterface(XNamed.class,
				xSpreadsheet);
		xsheetname.setName(sheetname);
	}
	
	/**
	 * Get rows object
	 * @param xSpreadsheet
	 * @return
	 * @throws Exception
	 */
	public static XTableRows getSCRows(XSpreadsheet xSpreadsheet) throws Exception {
		XColumnRowRange xColumnRowRange = 
				(XColumnRowRange) UnoRuntime.queryInterface(XColumnRowRange.class, xSpreadsheet);
		XTableRows xTableRows = xColumnRowRange.getRows();
		
		return xTableRows;
	}
	
	/**
	 * Get columns object
	 * @param xSpreadsheet
	 * @return
	 * @throws Exception
	 */
	public static XTableColumns getSCColumns(XSpreadsheet xSpreadsheet) throws Exception {
		XColumnRowRange xColumnRowRange = 
				(XColumnRowRange) UnoRuntime.queryInterface(XColumnRowRange.class, xSpreadsheet);
		XTableColumns xTableColumns = xColumnRowRange.getColumns();
		
		return xTableColumns;
	}
	
	/**
	 * Set floating number into specific cell 
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * @param value
	 * @throws Exception
	 */
	public static void setValueToCell(XSpreadsheet xSpreadsheet, int column, int row, double value) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		xCell.setValue(value);
	}
	
	/**
	 * Set text into specific cell
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * @param text
	 * @throws Exception
	 */
	public static void setTextToCell(XSpreadsheet xSpreadsheet, int column, int row, String text) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		XText xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
		xText.setString(text);
	}

	/**
	 * Set text into specific cell
	 * @param xCell
	 * @param text
	 * @throws Exception
	 */
	public static void setTextToCell(XCell xCell, String text) throws Exception {
		XText xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
		xText.setString(text);
	}
	
	/**
	 * Set formula into specific cell
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * @param formula
	 * @throws Exception
	 */
	public static void setFormulaToCell(XSpreadsheet xSpreadsheet, int column, int row, String formula) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		xCell.setFormula(formula);
	}
	
	/**
	 * Get value from specific cell
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * @return
	 * @throws Exception
	 */
	public static double getValueFromCell(XSpreadsheet xSpreadsheet, int column, int row) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		double cellValue = xCell.getValue();
		
		return cellValue;
	}
	
	/**
	 * Get text from specific cell
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * 
	 * @return
	 * @throws Exception
	 */
	public static String getTextFromCell(XSpreadsheet xSpreadsheet, int column, int row) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		XText xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
		
		return xText.getString();
	}
	
	/**
	 * Get formula string from specific cell
	 * @param xSpreadsheet
	 * @param column
	 * @param row
	 * @return
	 * @throws Exception
	 */
	public static String getFormulaFromCell(XSpreadsheet xSpreadsheet, int column, int row) throws Exception {
		XCell xCell = xSpreadsheet.getCellByPosition(column, row);
		String cellFormula = xCell.getFormula();
		
		return cellFormula;
	}
	
	/**
	 * Set numbers into a cell range
	 * @param xSpreadsheet
	 * @param start_col
	 * @param start_row
	 * @param end_col
	 * @param end_row
	 * @param values
	 * @throws Exception
	 */
	@Deprecated
	public static void setValueToCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, int end_col, int end_row,  double[][] values) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, end_col, end_row);
		XCell xCell = null;
		for (int i = 0; i <= (end_row - start_row); i++ ) {
			for(int j = 0; j <= (end_col - start_col); j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				xCell.setValue(values[i][j]);
			}
		}
	}
	
	public static void setValueToCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, double[][] values) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, start_col + values[0].length - 1, start_row + values.length - 1);
		XCell xCell = null;
		for (int i = 0; i < values.length; i++ ) {
			for(int j = 0; j < values[0].length; j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				xCell.setValue(values[i][j]);
			}
		}
	}
	
	/**
	 * Set text into a cell range
	 * @param xSpreadsheet
	 * @param start_col
	 * @param start_row
	 * @param end_col
	 * @param end_row
	 * @param texts
	 * @throws Exception
	 */
	@Deprecated  
	public static void setTextToCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, int end_col, int end_row,  String[][] texts) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, end_col, end_row);
		XCell xCell = null;
		XText xText = null;
		for (int i = 0; i <= (end_row - start_row); i++ ) {
			for(int j = 0; j <= (end_col - start_col); j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
				xText.setString(texts[i][j]);
			}
		}
	}
	
	public static void setTextToCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, String[][] texts) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, start_col + texts[0].length - 1, start_row + texts.length - 1);
		XCell xCell = null;
		XText xText = null;
		for (int i = 0; i < texts.length; i++ ) {
			for(int j = 0; j < texts[0].length; j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
				xText.setString(texts[i][j]);
			}
		}
	}
	
	/**
	 * Get number content from a cell range
	 * @param xSpreadsheet
	 * @param start_col
	 * @param start_row
	 * @param end_col
	 * @param end_row
	 * @return
	 * @throws Exception
	 */
	public static double[][] getValueFromCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, int end_col, int end_row) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, end_col, end_row);
		XCell xCell = null;
		double[][] cellValues = new double[end_row - start_row+1][end_col - start_col +1];
		
		for (int i = 0; i <= (end_row - start_row); i++ ) {
			for(int j = 0; j <= (end_col - start_col); j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				cellValues[i][j] = xCell.getValue();
			}
		}
		
		return cellValues;
	}
	
	/**
	 * Get text content from a cell range
	 * @param xSpreadsheet
	 * @param start_col
	 * @param start_row
	 * @param end_col
	 * @param end_row
	 * @return
	 * @throws Exception
	 */
	public static String[][] getTextFromCellRange(XSpreadsheet xSpreadsheet, int start_col, int start_row, int end_col, int end_row) throws Exception {
		XCellRange xCellRange = xSpreadsheet.getCellRangeByPosition(start_col, start_row, end_col, end_row);
		XCell xCell = null;
		XText xText = null;
		String[][] cellTexts = new String[end_row - start_row+1][end_col - start_col +1];
		
		for (int i = 0; i <= (end_row - start_row); i++ ) {
			for (int j = 0; j <= (end_col - start_col); j++) {
				xCell = xCellRange.getCellByPosition(j, i);
				xText = (XText) UnoRuntime.queryInterface(XText.class, xCell);
				cellTexts[i][j] = xText.getString();
			}
		}
		
		return cellTexts;
	}
		
	//TODO ZS - public static String[][] getAllFromCellRange
	
	/**
	 * Switch to specific sheet
	 * @param xSpreadsheetDocument
	 * @param xSpreadsheet
	 */
	public static void setCurrentSheet(XSpreadsheetDocument xSpreadsheetDocument, XSpreadsheet xSpreadsheet) throws Exception {
		XModel xModel = (XModel) UnoRuntime.queryInterface(XModel.class, xSpreadsheetDocument);
		XController xController = xModel.getCurrentController();
		XSpreadsheetView xSpreadsheetView = (XSpreadsheetView) UnoRuntime.queryInterface(XSpreadsheetView.class, xController);
		xSpreadsheetView.setActiveSheet(xSpreadsheet);
	}
	
	/**
	 * Get sheet object of current active sheet
	 * @param xSpreadsheetDocument
	 * @return
	 */
	public static XSpreadsheet getCurrentSheet(XSpreadsheetDocument xSpreadsheetDocument) throws Exception {
		XModel xModel = (XModel) UnoRuntime.queryInterface(XModel.class, xSpreadsheetDocument);
		XController xController = xModel.getCurrentController();
		XSpreadsheetView xSpreadsheetView = (XSpreadsheetView) UnoRuntime.queryInterface(XSpreadsheetView.class, xController);
		XSpreadsheet xSpreadsheet = xSpreadsheetView.getActiveSheet();
		
		return xSpreadsheet;
	}
	
	/**
	 * Get sheet object by sheet index
	 * 
	 * @param xSpreadsheetDocument
	 * @return
	 * @throws Exception
	 */
	public static String getSCActiveSheetName(
			XSpreadsheetDocument xSpreadsheetDocument) throws Exception {
		XModel xSpreadsheetModel = (XModel) UnoRuntime.queryInterface(
				XModel.class, xSpreadsheetDocument);
		XSpreadsheetView xSpeadsheetView = (XSpreadsheetView) UnoRuntime
				.queryInterface(XSpreadsheetView.class,
						xSpreadsheetModel.getCurrentController());
		XSpreadsheet activesheet = xSpeadsheetView.getActiveSheet();
		XNamed activesheetName = (XNamed) UnoRuntime.queryInterface(
				XNamed.class, activesheet);
		return activesheetName.getName();
	}
	
	/**
	 * Set specific property's value for an object
	 * @param obj
	 * @param propName
	 * @param value
	 * @throws Exception
	 */
	public static void setProperties(Object obj, String propName, Object value) throws Exception {
		XPropertySet xPropertySet = 
				(XPropertySet) UnoRuntime.queryInterface(XPropertySet.class, obj);
		xPropertySet.setPropertyValue(propName, value);
	}
	
	/**
	 * Get specific property's value of an object
	 * @param obj
	 * @param propName
	 * @return
	 * @throws Exception
	 */
	public static Object getProperties(Object obj, String propName) throws Exception {
		XPropertySet xPropertySet = 
				(XPropertySet) UnoRuntime.queryInterface(XPropertySet.class, obj);
		Object value = xPropertySet.getPropertyValue(propName);
		
		return value;
	}	
	
	/**
	 * Set value of specific property from a cell
	 * @param xCell
	 * @param propName
	 * @param value
	 * @throws Exception
	 */
	public static void setCellProperties(XCell xCell, String propName, Object value) throws Exception {
		
		setProperties(xCell, propName, value);
	}

	/**
	 * Get value of specific property from a cell
	 * @param xCell
	 * @param propName
	 * @return
	 * @throws Exception
	 */
	public static Object getCellProperties(XCell xCell, String propName) throws Exception {
			return getProperties(xCell, propName);
	}
		
	/**
	 * Save file after open file. 
	 * @param xSpreadsheetDocument
	 * @throws Exception
	 */
	public static void save(XSpreadsheetDocument xSpreadsheetDocument)
			throws Exception {
		XStorable scStorable = (XStorable) UnoRuntime.queryInterface(
				XStorable.class, xSpreadsheetDocument);
		scStorable.store();
	}

	
	/**
	 * Close specific opening spreadsheet file which has been saved
	 * @param xSpreadsheetDocument
	 * @throws Exception
	 */
	public static void closeFile(XSpreadsheetDocument xSpreadsheetDocument) throws Exception {
		XCloseable xCloseable = (XCloseable) UnoRuntime.queryInterface(XCloseable.class, xSpreadsheetDocument);
		xCloseable.close(false);
	}
		
	/**
	 * Initial the filter name list
	 * @throws Exception
	 */
	private static void initFilterName() throws Exception {
		if (filterName.size() > 0) {
			return;
		}
		
		filterName.put("ods", "calc8");
		filterName.put("ots", "calc8_template");
		filterName.put("xls", "MS Excel 97");
		filterName.put("xlt", "MS Excel 97 Vorlage/Template");
		filterName.put("csv", "Text - txt - csv (StarCalc)");
	}
	
	
	/***************************************************************
	 *      Chart Utility method - using chart interface           *
	****************************************************************/

	/**
	 * Get a CellRangeAddress by cell range reference name
	 * @param xSpreadsheet
	 * @param rangeName    a cell range reference name(e.g. "A1:B2")
	 * @return
	 */
	public static CellRangeAddress getChartDataRangeByName(XSpreadsheet xSpreadsheet, String rangeName) {
		XCellRange cellRange = xSpreadsheet.getCellRangeByName(rangeName);
		XCellRangeAddressable xCellRangeAddressable = 
			(XCellRangeAddressable) UnoRuntime.queryInterface(XCellRangeAddressable.class, cellRange);
	
		CellRangeAddress cellRangeAddress = xCellRangeAddressable.getRangeAddress();
		return cellRangeAddress;
	}
	
	/**
	 * Create a spreadsheet chart with data in a specific cell range.
	 * @param xSpreadsheet
	 * @param rec   a rectangle shape object
	 * @param dataRangeAddress   the CellRangeAddress array of chart data source
	 * @param chartName
	 * @return
	 * @throws Exception
	 */
	public static XChartDocument createChart(XSpreadsheet xSpreadsheet, Rectangle rec, CellRangeAddress[] dataRangeAddress, String chartName) throws Exception {
		
		return createChart(xSpreadsheet, rec, dataRangeAddress, chartName, true, false);
	}
	
	/**
	 * Create a spreadsheet chart with data in a specific cell range with column/row label enable/not.
	 * @param xSpreadsheet
	 * @param rec    a rectangle shape object
	 * @param dataRangeAddress    the CellRangeAddress array of chart data source
	 * @param chartName
	 * @param hasColumnLabel  
	 * @param hasRowLabel
	 * @return
	 * @throws Exception
	 */
	public static XChartDocument createChart(XSpreadsheet xSpreadsheet, Rectangle rec, CellRangeAddress[] dataRangeAddress, String chartName, Boolean hasColumnLabel, Boolean hasRowLabel) throws Exception {
		XChartDocument xChartDocument = null;
		XTableChartsSupplier xTChartSupplier = 
				(XTableChartsSupplier) UnoRuntime.queryInterface(XTableChartsSupplier.class, xSpreadsheet);
		XTableCharts xTableCharts = xTChartSupplier.getCharts();
		XNameAccess xNameAccess = 
				(XNameAccess) UnoRuntime.queryInterface(XNameAccess.class, xTableCharts);
		if (xNameAccess != null && !xNameAccess.hasByName(chartName)) {
			
			xTableCharts.addNewByName(chartName, rec, dataRangeAddress, hasColumnLabel, hasRowLabel);
			XTableChart xTableChart = (XTableChart) UnoRuntime.queryInterface(
					XTableChart.class, xNameAccess.getByName(chartName));
			XEmbeddedObjectSupplier xEmbeddedObjectSupplier = (XEmbeddedObjectSupplier) UnoRuntime.queryInterface(
					XEmbeddedObjectSupplier.class, xTableChart);
			xChartDocument = (XChartDocument) UnoRuntime.queryInterface(
					XChartDocument.class, xEmbeddedObjectSupplier.getEmbeddedObject());
		}
		
		return xChartDocument;
	}
	
	/**
	 * Get XChartDocument object via the chart name.
	 * @param xSpreadsheet
	 * @param chartName
	 * @return
	 * @throws Exception
	 */
	public static XChartDocument getChartByName(XSpreadsheet xSpreadsheet, String chartName) throws Exception {
		XChartDocument xChartDocument = null;
		XTableChartsSupplier xTChartSupplier = 
				(XTableChartsSupplier) UnoRuntime.queryInterface(XTableChartsSupplier.class, xSpreadsheet);
		XTableCharts xTableCharts = xTChartSupplier.getCharts();
		XNameAccess xNameAccess = 
				(XNameAccess) UnoRuntime.queryInterface(XNameAccess.class, xTableCharts);
		
		if (xNameAccess != null && xNameAccess.hasByName(chartName)) {
			XTableChart xTableChart = (XTableChart) UnoRuntime.queryInterface(
					XTableChart.class, xNameAccess.getByName(chartName));
			XEmbeddedObjectSupplier xEmbeddedObjectSupplier = (XEmbeddedObjectSupplier) UnoRuntime.queryInterface(
					XEmbeddedObjectSupplier.class, xTableChart);
			xChartDocument = (XChartDocument) UnoRuntime.queryInterface(
					XChartDocument.class, xEmbeddedObjectSupplier.getEmbeddedObject());
		}
		
		return xChartDocument;
	}
	
	/**
	 * Set specific basic type to chart
	 * @param xChartDocument
	 * @param chartType
	 * @throws Exception
	 */
	public static void setChartType(XChartDocument xChartDocument, String chartType) throws Exception {
		XMultiServiceFactory xMultiServiceFactory = (XMultiServiceFactory) UnoRuntime.queryInterface(
			XMultiServiceFactory.class, xChartDocument);
		XDiagram xDiagram = (XDiagram) UnoRuntime.queryInterface(
			XDiagram.class, xMultiServiceFactory.createInstance(chartType));
		xChartDocument.setDiagram(xDiagram);
	}
	
	/**
	 * Get the type string of a chart
	 * @param xChartDocument
	 * @return
	 * @throws Exception
	 */
	public static String getChartType(XChartDocument xChartDocument) throws Exception {
		return xChartDocument.getDiagram().getDiagramType();
	}
	
	/**
	 * Get the names of charts in specific sheet
	 * @param xSpreadsheet
	 * @return
	 * @throws Exception
	 */
	public static String[] getChartNameList(XSpreadsheet xSpreadsheet) throws Exception {
		XTableChartsSupplier xTChartSupplier = 
				(XTableChartsSupplier) UnoRuntime.queryInterface(XTableChartsSupplier.class, xSpreadsheet);
		XTableCharts xTableCharts = xTChartSupplier.getCharts();
		String[] chartNames = xTableCharts.getElementNames();
		return chartNames;
	}
	


}