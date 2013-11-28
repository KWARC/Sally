package info.kwarc.sally.spreadsheet3.extraction;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class AEResults {
		
	public class CellAreaRepresentation {
		private StructureType type;
		private List<Integer> indices;
		
		public CellAreaRepresentation(StructureType type) {
			super();
			this.type = type;
			this.indices = new ArrayList<Integer>();
		}

		public StructureType getType() {
			return type;
		}

		public void setType(StructureType type) {
			this.type = type;
		}

		public List<Integer> getIndices() {
			return indices;
		}
		
		public void setIndex(Integer index) {
			this.indices.clear();
			this.indices.add(index);
		}
		
		public void addIndex(Integer index) {
			if (!this.indices.contains(index))
				this.indices.add(index);
		}
		
		public void addIndices(List<Integer> indices) {
			for (Integer index : indices)
				addIndex(index);
		}
		
		public Boolean sameIndexAs(CellAreaRepresentation cell) {
			return ( (this.getIndices().size() == 1) && (cell.getIndices().size() == 1) &&
				     (this.getIndices().get(0) == cell.getIndices().get(0)) );
		}
	}
	
	final Logger logger = LoggerFactory.getLogger(AEResults.class);
	
	String sheet;
	int rows, columns;
	int maxIndex;
	CellAreaRepresentation[][] cellAreaRepresentation;
	
	public AEResults(String sheet, int rows, int columns) {
		super();
		this.sheet = sheet;
		this.rows = rows;
		this.columns = columns;
		maxIndex = 0;
		cellAreaRepresentation = new CellAreaRepresentation[rows][];
		for (int row = 0; row < rows; row++) {
			cellAreaRepresentation[row] = new CellAreaRepresentation[columns];
			for (int column = 0; column < columns; column++)
				cellAreaRepresentation[row][column] = new CellAreaRepresentation(StructureType.UNKNOWN);
		}
	}
	
	public Boolean hasId(int row, int column) {
		return (!cellAreaRepresentation[row][column].getIndices().isEmpty());
	}
	
	public void addArea(AreaInformation area) {
		for (RangeCoordinates range : area.getRanges()) {
			for (int row = range.getStartRow(); row <= range.getEndRow(); row++) {
				for (int column = range.getStartColumn(); column <= range.getEndColumn(); column++) {
					addIndex(area.getId(), area.getType(), row, column);
				}
			}
		}
	}
	
	public void addIndex(int index, StructureType type, int row, int column) {
		if (cellAreaRepresentation[row][column].getType().equals(StructureType.UNKNOWN) && cellAreaRepresentation[row][column].getIndices().isEmpty())
			cellAreaRepresentation[row][column].setType(type);
		else if (!cellAreaRepresentation[row][column].getType().equals(StructureType.UNKNOWN) && 
				!type.equals(StructureType.UNKNOWN) &&
				!cellAreaRepresentation[row][column].getType().equals(type) )
			cellAreaRepresentation[row][column].setType(StructureType.UNKNOWN);
		
		cellAreaRepresentation[row][column].addIndex(index);
		if (index > maxIndex)
			maxIndex = index;
			
	}
	
	public void addIndices(List<Integer> indices, StructureType type, int row, int column) {
		if (cellAreaRepresentation[row][column].getType().equals(StructureType.UNKNOWN) && cellAreaRepresentation[row][column].getIndices().isEmpty())
			cellAreaRepresentation[row][column].setType(type);
		else if (!cellAreaRepresentation[row][column].getType().equals(StructureType.UNKNOWN) && 
				!type.equals(StructureType.UNKNOWN) &&
				!cellAreaRepresentation[row][column].getType().equals(type) )
			cellAreaRepresentation[row][column].setType(StructureType.UNKNOWN);
		
		cellAreaRepresentation[row][column].addIndices(indices);
		for (Integer index : indices)
			if (index > maxIndex)
				maxIndex = index;
	}
	
	public void add(AEResults map) {
		if ( (map.getRows() == this.getRows()) && (map.getColumns() == this.getColumns()) ) {
			for (int row = 0; row < rows; row++) {
				for (int column = 0; column < columns; column++) {
					addIndices(map.getRep(row, column).getIndices(), map.getRep(row, column).getType(), row, column);
				}
			}
		}
	}

	public List<AreaInformation> getAreas() {
		Map<Integer, AreaInformation> idAreaMap = new HashMap<Integer,AreaInformation>();
		
		Boolean[][] visited = new Boolean[rows][];
		for (int row = 0; row < rows; row++) {
			visited[row] = new Boolean[columns];
			for (int column = 0; column < columns; column++) {
				visited[row][column] = false;
			}
		}

		for (int row = 0; row < rows; row++) {
			for (int column = 0; column < columns; column++) {
				if (!visited[row][column] && (cellAreaRepresentation[row][column].getIndices().size() == 1) ) {
					
					// Expand area to the right and then to the bottom
					int endColumn = column;
					while ((endColumn+1 < columns) && cellAreaRepresentation[row][column].sameIndexAs(cellAreaRepresentation[row][endColumn+1]) )
						endColumn++;
					
					// Now expand to the bottom
					int endRow = row;
					Boolean expand = true;
					while (expand && (endRow+1 < rows)) {
						Boolean allValid = true;
						Boolean sameIDFound = false;
						for(int j = column; j <= endColumn; j++) {
							if ( !cellAreaRepresentation[endRow+1][j].getIndices().isEmpty() &&
								 !cellAreaRepresentation[row][column].sameIndexAs(cellAreaRepresentation[endRow+1][j]) )		
								allValid = false;
							if ( cellAreaRepresentation[row][column].sameIndexAs(cellAreaRepresentation[endRow+1][j]) )
								sameIDFound = true;
						}
						if (allValid && sameIDFound)
							endRow++;
						else
							expand = false;
					}
					
					// Add area and mark area as visited
					Integer cellId = cellAreaRepresentation[row][column].getIndices().get(0);
					
					if (idAreaMap.containsKey(cellId))
						idAreaMap.get(cellId).addRange(new RangeCoordinates(this.sheet, row, column, endRow, endColumn));
					else {
						
						AreaInformation ai = new AreaInformation(cellAreaRepresentation[row][column].getType(), cellAreaRepresentation[row][column].getIndices().get(0) );
						ai.addRange(new RangeCoordinates(this.sheet, row, column, endRow, endColumn) );
						idAreaMap.put(ai.getId(), ai);
					}
					
					for (int i = row; i <= endRow; i++)
						for (int j = column; j <= endColumn; j++)
							visited[i][j] = true;
				}
			}
		}
				
		return new ArrayList<AreaInformation>(idAreaMap.values());
	}
	

	public List<AmbiguousInformation> getAmbiguous() {
		List<AmbiguousInformation> ai = new ArrayList<AmbiguousInformation>();
		for (int row = 0; row < rows; row++) {
			for (int column = 0; column < columns; column++) {
				if ( (cellAreaRepresentation[row][column].getIndices() != null) && 
				     (cellAreaRepresentation[row][column].getIndices().size() > 1) ) {
					ai.add( new AmbiguousInformation(sheet, row, column, cellAreaRepresentation[row][column].getIndices()) );
				}
			}
		}
		
		return ai;
	}
	
	public CellAreaRepresentation getRep(int row, int column) {
		return cellAreaRepresentation[row][column];
	}
	
	public void setIndex(int startRow, int startColumn, int endRow, int endColumn, int index) {
		for (int row = startRow; row <= endRow; row++) {
			for (int column = startColumn; column <= endColumn; column++) {
				cellAreaRepresentation[row][column].setIndex(index);
			}
		}
	}
	
	public void setType(int startRow, int startColumn, int endRow, int endColumn, StructureType type) {
		for (int row = startRow; row <= endRow; row++) {
			for (int column = startColumn; column <= endColumn; column++) {
				cellAreaRepresentation[row][column].setType(type);
			}
		}
	}
	
	public int getRows() {
		return rows;
	}
	
	public int getColumns() {
		return columns;
	}
	
	public int getMaxIndex() {
		return maxIndex;
	}
	
	@Override
	public String toString() {
		String out = "";
		for (AreaInformation area : getAreas()) {
			out += "Area with id " + area.getId() + " and type " + area.getType().name() + "\n";
			for (RangeCoordinates range : area.getRanges())
				out += "    (" + range.getStartRow() + "/" + range.getStartColumn() + ") - (" + range.getEndRow() + "/" + range.getEndColumn() + ")\n";
		}
		out += "Ambiguous cells:\n";
		for (AmbiguousInformation ambig : getAmbiguous() ) {
			String cellAmbigInfo = "";
			cellAmbigInfo += "Cell (" + ambig.getRow() + "/" + ambig.getColumn() + "): ";
			for (Integer id : ambig.getRelatedAreas())
				cellAmbigInfo += id + "  ";
			out += cellAmbigInfo + "\n";
		}
		return out;
	}
	
	/*
	public void print(PrintWriter out) {
		out.println("Printing areas:");
		for (AreaInformation area : getAreas()) {
			out.println("Area with id " + area.getId() + " and type " + area.getType().name());
			for (RangeCoordinates range : area.getRanges())
				out.println("    (" + range.getStartRow() + "/" + range.getStartColumn() + ") - (" + range.getEndRow() + "/" + range.getEndColumn() + ")");
		}
		out.println("Ambiguous cells:");
		for (AmbiguousInformation ambig : getAmbiguous() ) {
			String cellAmbigInfo = "";
			cellAmbigInfo += "Cell (" + ambig.getRow() + "/" + ambig.getColumn() + "): ";
			for (Integer id : ambig.getRelatedAreas())
				cellAmbigInfo += id + "  ";
			out.println(cellAmbigInfo);
		}
	}
	
	public void print() {
		System.out.println("Here are the results");
		print(new PrintWriter(System.out));
	}*/
}
