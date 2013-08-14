package info.kwarc.sally.spreadsheet2;


public class WinogradData {

	public static FormalSpreadsheet getFormalWinograd() {
		FormalSpreadsheet spreadsheet = new FormalSpreadsheet();
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,0), "Costs", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,1,2,1), "Actual", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,3,2,1), "Projected", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,1), "1984", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,2), "1985", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,3), "1986", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,4), "1987", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,0), "c1", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,0), "c2", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,0), "total", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,1), "0.1", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,2), "0.2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,3), "0.3", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,4), "0.4", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,1), "1.1", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,2), "1.2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,3), "1.3", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,4), "1.4", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,1), "1.2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,2), "1.4", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,3), "1.6", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,4), "1.8", ContentValueType.FLOAT);
		
		return spreadsheet;
	}


}
