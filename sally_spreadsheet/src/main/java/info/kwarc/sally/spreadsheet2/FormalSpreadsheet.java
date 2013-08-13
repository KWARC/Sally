package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class FormalSpreadsheet {
	int id;
	List<String> worksheets;
	Map<CellSpaceInformation, FormalSsElement> data;
	Map<String, Integer> maxRow;
	Map<String, Integer> maxColumn;
	
	public FormalSpreadsheet() {
		super();
		this.worksheets = new ArrayList<String>();
		this.id = 0;
		this.data = new HashMap<CellSpaceInformation, FormalSsElement>();
		this.maxRow = new HashMap<String,Integer>();
		this.maxColumn = new HashMap<String,Integer>();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((data == null) ? 0 : data.hashCode());
		result = prime * result + id;
		result = prime * result
				+ ((maxColumn == null) ? 0 : maxColumn.hashCode());
		result = prime * result + ((maxRow == null) ? 0 : maxRow.hashCode());
		result = prime * result
				+ ((worksheets == null) ? 0 : worksheets.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FormalSpreadsheet other = (FormalSpreadsheet) obj;
		if (data == null) {
			if (other.data != null)
				return false;
		} else if (!data.equals(other.data))
			return false;
		if (id != other.id)
			return false;
		if (maxColumn == null) {
			if (other.maxColumn != null)
				return false;
		} else if (!maxColumn.equals(other.maxColumn))
			return false;
		if (maxRow == null) {
			if (other.maxRow != null)
				return false;
		} else if (!maxRow.equals(other.maxRow))
			return false;
		if (worksheets == null) {
			if (other.worksheets != null)
				return false;
		} else if (!worksheets.equals(other.worksheets))
			return false;
		return true;
	}

	public FormalSsElement get(CellSpaceInformation position) {
		if (data.containsKey(position))
			return data.get(position);
		else
			return null;
	}
	
	public int getMaxRow(String worksheet) {
		if (maxRow.containsKey(worksheet))
			return maxRow.get(worksheet);
		else
			return -1;
	}
	
	public int getMaxColumn(String worksheet) {
		if (maxColumn.containsKey(worksheet))
			return maxColumn.get(worksheet);
		else
			return -1;
	}
	
	public List<CellSpaceInformation> getAllPositions() {
		return new ArrayList<CellSpaceInformation>(data.keySet());
	}
	
	public void setContent(CellSpaceInformation position, String value, ContentValueType valueType) {
		data.put(position, new FormalSsElement(position, value, valueType) );
		id++;
		if (!worksheets.contains( position.getWorksheet()))
			worksheets.add(position.getWorksheet());
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
