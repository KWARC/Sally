package info.kwarc.sally.spreadsheet3.extraction;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class FeatureMaps {
	private Map<String, Integer[][]> maps = new HashMap<String, Integer[][]>();
	private int rows, columns;
	
	final Logger logger = LoggerFactory.getLogger(FeatureMaps.class);
	
	public FeatureMaps(int rows, int columns) {
		this.rows = rows;
		this.columns = columns;
	}
	
	public Integer[][] createMap(String name) {
		Integer[][] map = new Integer[rows][];
		for (int i = 0; i < rows; i++)
			map[i] = new Integer[columns];
		maps.put(name, map);
		return map;
	}
	
	public Integer[][] createMap(String name, Integer value) {
		Integer[][] map = createMap(name);
		for (int row = 0; row < rows; row++)
			for (int column = 0; column < columns; column++)
				map[row][column] = new Integer(value);
		return map;
	}
	
	public Boolean addMap(String name, Integer[][] map) {
		if (map.length == rows) {
			Boolean correctWidth = true;
			for (int i = 0; i < map.length; i++)
				if (map[i].length != columns)
					correctWidth = false;
			if (correctWidth) {
				maps.put(name, map);
				return true;
			} else
				return false;
		} else
			return false;
	}
	
	public Integer[][] getMapByName(String name) {
		if (maps.containsKey(name))
			return maps.get(name);
		else
			return null;
	}
	
	public Iterator<Integer[][]> getMaps() {
		return maps.values().iterator();
	}
	
	public int getRows() {
		return rows;
	}
	
	public int getColumns() {
		return columns;
	}
	
	public Boolean sameFeatures(int row1, int column1, int row2, int column2) {
		Boolean allEqual = true;
		Iterator<Integer[][]> it = getMaps();
		while (it.hasNext()) {
			Integer[][] map = it.next();
			if ((map[row1][column1] != null) && (map[row2][column2] != null) && (!map[row1][column1].equals(map[row2][column2])))
				allEqual = false;
		}
		return allEqual;
	}
	
	public void printMap(String name) {
		Integer[][] map = getMapByName(name);
		if (map != null) {
			System.out.println("-------------------------------------------");
			System.out.println("       " + name);
			System.out.println("-------------------------------------------");
			for (int row = 0; row < map.length; row++) {
				for (int column = 0; column < map[row].length; column++) {
					System.out.print("(" + row + "/" + column + ")" + ": " + map[row][column] + " | ");
				}
				System.out.println();	
			}
		}
	}
	
	public void printAllMaps() {
		for (String name : maps.keySet())
			printMap(name);
	}
}
