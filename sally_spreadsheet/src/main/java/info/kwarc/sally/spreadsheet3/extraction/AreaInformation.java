package info.kwarc.sally.spreadsheet3.extraction;


import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.util.ArrayList;
import java.util.List;


public class AreaInformation {
	private StructureType type;
	private int id;
	private List<RangeCoordinates> ranges;
	
	public AreaInformation(StructureType type, int id) {
		super();
		ranges = new ArrayList<RangeCoordinates>();
		this.type = type;
		this.id = id;
	}
	
	public AreaInformation(StructureType type, int id, RangeCoordinates range) {
		super();
		this.type = type;
		this.id = id;
		ranges = new ArrayList<RangeCoordinates>();
		ranges.add(range);
	}

	public StructureType getType() {
		return type;
	}
	
	public int getId() {
		return id;
	}
	
	public void addRange(RangeCoordinates range) {
		ranges.add(range);
	}

	public List<RangeCoordinates> getRanges() {
		return ranges;
	}
	
	public int getDistanceFrom(CellSpaceInformation pos) {
		int distance = Integer.MAX_VALUE;
		for (RangeCoordinates range : ranges)
			distance = java.lang.Math.min(range.getDistanceFrom(pos), distance);
		return distance;
	}
	
	public int getStartRow() {
		int distance = Integer.MAX_VALUE;
		for (RangeCoordinates range : ranges)
			distance = java.lang.Math.min(range.getStartRow(), distance);
		return distance;
	}
	
	public int getStartColumn() {
		int distance = Integer.MAX_VALUE;
		for (RangeCoordinates range : ranges)
			distance = java.lang.Math.min(range.getStartColumn(), distance);
		return distance;
	}
	public int getEndRow() {
		int distance = Integer.MIN_VALUE;
		for (RangeCoordinates range : ranges)
			distance = java.lang.Math.max(range.getEndRow(), distance);
		return distance;
	}
	
	public int getEndColumn() {
		int distance = Integer.MIN_VALUE;
		for (RangeCoordinates range : ranges)
			distance = java.lang.Math.max(range.getEndColumn(), distance);
		return distance;
	}
	
	public boolean isAbove(AreaInformation a) {
		return ((this.getEndRow() < a.getStartRow() ) && (this.getStartColumn() <= a.getEndColumn()) && (this.getEndColumn() >= a.getStartColumn()) );
	}
	
	public boolean isLeftFrom(AreaInformation a) {
		return ((this.getEndColumn() < a.getStartColumn() ) && (this.getStartRow() <= a.getEndRow()) && (this.getEndRow() >= a.getStartRow()) );
	}

}
