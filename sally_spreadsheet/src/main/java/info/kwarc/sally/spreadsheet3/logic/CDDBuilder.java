package info.kwarc.sally.spreadsheet3.logic;

import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;

import java.util.ArrayList;
import java.util.List;

/**
 * A CDD builder provides an interface to build CellDependencyDescription classes for standard use cases.
 * @author cliguda
 *
 */
public class CDDBuilder {
	
	/** 
	 * Create a CellDependencyDescription for a typical functional relation.
	 * It assumes, that some blocks are above the last block and all others are on the left side. Each cell in the last block is associated with the cells that are 
	 * in the same row or column.
	 */
	public static CellDependencyDescription createCDDFunctionalRelation(List<Block> blocks) {
		
		int maxX = 0;
		int maxY = 0;
		String cellRelation = "";
		for (Block b : blocks) {
			maxX = java.lang.Math.max(maxX, b.getMaxRow()-b.getMinRow());
			maxY = java.lang.Math.max(maxY, b.getMaxColumn()-b.getMinColumn());
		}
		
		List<Integer> orientationTypes = getOrientationTypes(blocks);
		for (int i = 0; i < orientationTypes.size(); i++) {
			if (orientationTypes.get(i) == 0)
				cellRelation = cellRelation + "x,0;";
			else if (orientationTypes.get(i) == 1)
				cellRelation = cellRelation + "0,y;";
			else
				throw new java.lang.IllegalArgumentException("No valid orientation type.");
		}
		cellRelation = cellRelation + "x,y";
		
		return new CellDependencyDescription(0, maxX, 0, maxY, cellRelation);
	}
	
	private static List<Integer> getOrientationTypes(List<Block> blocks) {
		List<Integer> orientationTypes = new ArrayList<Integer>();
		Block fb = blocks.get(blocks.size()-1);
		
		for (int i = 0; i < blocks.size()-1; i++) {
			if (blocks.get(i).getMaxRow() < fb.getMinRow())
				orientationTypes.add(0);
			else if (blocks.get(i).getMaxColumn() < fb.getMinColumn())
				orientationTypes.add(1);
			else
				throw new java.lang.IllegalArgumentException("No valid orientation found.");
		}
		
		return orientationTypes;
	}

}
