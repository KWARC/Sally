package info.kwarc.sissi.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class FormalSpreadsheet {
	int worksheets, id;
	Map<CellSpaceInformation, FormalSsElement> data;
	Map<Integer, Integer> maxRow;
	Map<Integer, Integer> maxColumn;
	

	public FormalSpreadsheet() {
		super();
		this.worksheets = 0;
		this.id = 0;
		this.data = new HashMap<CellSpaceInformation, FormalSsElement>();
		this.maxRow = new HashMap<Integer,Integer>();
		this.maxColumn = new HashMap<Integer,Integer>();
	}
	
	public FormalSsElement get(CellSpaceInformation position) {
		if (data.containsKey(position))
			return data.get(position);
		else
			return null;
	}
	
	public int getMaxRow(int worksheet) {
		if (maxRow.containsKey(worksheet))
			return maxRow.get(worksheet);
		else
			return -1;
	}
	
	public int getMaxColumn(int worksheet) {
		if (maxColumn.containsKey(worksheet))
			return maxColumn.get(worksheet);
		else
			return -1;
	}
	
	public List<CellSpaceInformation> getAllPositions() {
		return new ArrayList<CellSpaceInformation>(data.keySet());
	}
	
	public FormalSsElement getContent(CellSpaceInformation pos) {
		return data.get(pos);
	}
	
	public void setContent(CellSpaceInformation position, String value, ContentValueType valueType) {
		data.put(position, new FormalSsElement(id, value, valueType, new ArrayList<CellSpaceInformation>()) );
		id++;
		worksheets = java.lang.Math.max(worksheets, position.getWorksheet());
		if (maxRow.containsKey(position.getWorksheet())) {
			if (position.getRow() > maxRow.get(position.getWorksheet()) )
				maxRow.put(position.getWorksheet(), position.getRow());
		} else
			maxRow.put(position.getWorksheet(), position.getRow());
		
		if (maxColumn.containsKey(position.getWorksheet())) {
			if (position.getColumn() > maxColumn.get(position.getWorksheet()) )
				maxColumn.put(position.getWorksheet(), position.getColumn());
		} else {
			maxColumn.put(position.getWorksheet(), position.getColumn());
		}
	}
	
	// TODO: Formulae
	public void setContent(CellSpaceInformation position, String value, ContentValueType valueType, List<CellSpaceInformation> parameters) {
		data.put(position, new FormalSsElement(id, value, valueType, parameters) );
		id++;
		worksheets = java.lang.Math.max(worksheets, position.getWorksheet());
		if (maxRow.containsKey(position.getWorksheet())) {
			if (position.getRow() > maxRow.get(position.getWorksheet()) )
				maxRow.put(position.getWorksheet(), position.getRow());
		} else
			maxRow.put(position.getWorksheet(), position.getRow());
		
		if (maxColumn.containsKey(position.getWorksheet())) {
			if (position.getColumn() > maxColumn.get(position.getWorksheet()) )
				maxColumn.put(position.getWorksheet(), position.getColumn());
		} else {
			maxColumn.put(position.getWorksheet(), position.getColumn());
		}
	}

}
