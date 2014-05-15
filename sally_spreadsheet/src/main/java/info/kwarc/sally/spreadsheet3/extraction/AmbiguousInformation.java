package info.kwarc.sally.spreadsheet3.extraction;

import java.util.List;

/**
 * If a cell can not be assigned to an unique area, the ambiguous informations are hold in this class.
 * @author cliguda
 *
 */
public class AmbiguousInformation {
	String sheet;
	int row, column;
	List<Integer> relatedAreas;
	
	public AmbiguousInformation(String sheet, int row, int column, List<Integer> relatedAreas) {
		super();
		this.sheet = sheet;
		this.row = row;
		this.column = column;
		this.relatedAreas = relatedAreas;
	}
	
	public String getSheet() {
		return sheet;
	}

	public int getRow() {
		return row;
	}

	public int getColumn() {
		return column;
	}

	public List<Integer> getRelatedAreas() {
		return relatedAreas;
	}
	
	public Boolean relatedTo(Integer index) {
		return relatedAreas.contains(index);
	}
	
	public void addIndex(Integer index) {
		relatedAreas.add(index);
	}
	
	public void addIndices(List<Integer> indices) {
		relatedAreas.addAll(indices);
	}
	
		
}
