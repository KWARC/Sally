package info.kwarc.sally.spreadsheet3.logic;

import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RelationBuilder {
	
	static Pattern numberPattern = Pattern.compile("\\d+");
	static Pattern additionPattern = Pattern.compile("(\\d+)\\+(\\d)");
	static Pattern subtractPattern = Pattern.compile("(\\d+)\\-(\\d)");
	
	public static List<CellTuple> createCellRelation(List<Block> blocks, List<CellDependencyDescription> descriptions) {
		List<CellTuple> cellDependencies = new ArrayList<CellTuple>();
		
		for (CellDependencyDescription description : descriptions) {
			for (int i = description.getMinX(); i <= description.getMaxX(); i++ ) {
				for (int j = description.getMinY(); j <= description.getMaxY(); j++) {
					String[] positionDesriptions = description.getCellRelation().split(";");
					if (positionDesriptions.length != blocks.size())
						throw new java.lang.IllegalArgumentException("Number of patterns is not equal to the number of blocks.");
					
					List<CellSpaceInformation> tuple = new ArrayList<CellSpaceInformation>();
					for (int pos = 0; pos < blocks.size(); pos++) {
						String[] tupleExpression = positionDesriptions[pos].split(",");
						if (tupleExpression.length != 2)
							throw new java.lang.IllegalArgumentException("Pattern has not the format \"expression,expression\".");
						tuple.add(blocks.get(pos).getCellForIndex(parseExpression(tupleExpression[0].replaceAll("x", new Integer(i).toString()).replaceAll("y", new Integer(j).toString())), 
								parseExpression(tupleExpression[1].replaceAll("x", new Integer(i).toString()).replaceAll("y", new Integer(j).toString()))));
					}
					cellDependencies.add(new CellTuple(tuple));
				}
			}
		}
		
		return cellDependencies;
	}
	
	private static int parseExpression(String expr) {
		Matcher numberMatcher = numberPattern.matcher(expr);
		Matcher additionMatcher = additionPattern.matcher(expr);
		Matcher subtractMatcher = subtractPattern.matcher(expr);
		if (numberMatcher.matches())
			return Integer.parseInt(expr);
		else if (additionMatcher.matches())
			return (Integer.parseInt(additionMatcher.group(1)) + Integer.parseInt(additionMatcher.group(2)) );
		else if (subtractMatcher.matches())
			return (Integer.parseInt(subtractMatcher.group(1)) - Integer.parseInt(subtractMatcher.group(2)) );
		else throw new java.lang.IllegalArgumentException("Expression has no valid format. Numbers and single additions and subtractions are allowed.");
	}

}
