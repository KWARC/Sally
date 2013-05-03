package info.kwarc.sally.model.document.spreadsheet;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Util {
	
	/*public static RangeCoordinates convertRange(String range) {
		Pattern p = Pattern.compile("([A-Z]+)([0-9]+):([A-Z]+)([0-9]+)");
		Matcher m = p.matcher(range);

		if (m.find()) {
			return new RangeCoordinates(Integer.parseInt(m.group(2))-1, convertRangeCharacter(m.group(1)), Integer.parseInt(m.group(4))-1, convertRangeCharacter(m.group(3)));
		} else
			return null;
	}*/

	public static CellInformation[] convertToLine(CellInformation[][] cells) {
		if (cells.length == 1) {
			// we're dealing a 1 row array 
			return cells[0];
		}
		if (cells[0].length == 1) {
			// we're dealing a 1 column array 
			CellInformation []result = new CellInformation[cells.length];
			for (int i=0; i<cells.length; ++i) {
				result[i] = cells[i][0];
			}
			return result;
		}
		throw new IllegalArgumentException("Convertion from a 2 Dim array with multiple lines and columns to a 1 Dim array failed");
	}
	
	public static CellSpaceInformation convertCellPosition(String position)  {
		Pattern p = Pattern.compile("([A-Z]+)([0-9]+)");
		Matcher m = p.matcher(position);

		if (m.find()) {
			return new CellSpaceInformation(Integer.parseInt(m.group(2))-1, convertRangeCharacter(m.group(1)));
		} else
			return null;	
	}
	
	public static int convertRangeCharacter(String str) {
		int valueA = (int) 'A';
		int index = 0;
		for (int i = 1; i <= str.length(); i++) {
			char c = str.charAt(i-1);
			int value = (int) c;
			index += (value - valueA + 1) * Math.pow(26, str.length() - i);
		}
		return (index-1);
	}
	
	public static String convertIndex2RangeCharacter(int index) {
		int valueA = (int) 'A';
		String character = "";
		int maxBase = 0;
		int maxValue = 26;
		while (index >= maxValue) {
			maxBase++;
			maxValue += Math.pow(26, maxBase+1);
		}
		for (int base = maxBase; base >= 0; base--) {
			int value = (int) (index / Math.pow(26, base));
			index = index - (value * (int)Math.pow(26, base));
			if (base > 0) {
				value--;	// To normalize between 0 and 25
			}
			char c = (char) (valueA + value);
			character += c;
		}
		return character;
	}
	
	
	public static CellInformation[][] extendArray(CellInformation[] array, int intoDimension) {
		CellInformation[][] extendedArray;
		
		if (intoDimension == 1) {
			extendedArray = new CellInformation[array.length][1];
			for (int i = 0; i < array.length; i++)
				extendedArray[i][0] = array[i];
		} else if (intoDimension == 2) {
			extendedArray = new CellInformation[1][array.length];
			for (int i = 0; i < array.length; i++)
				extendedArray[0][i] = array[i];
		} else
			throw new java.lang.IllegalArgumentException("Wrong parameter intoDimension. Must be 1 or 2");
		return extendedArray;
	}
	
	public static Boolean isHorizontal(CellInformation[] cellInformation) {
		if (cellInformation[0].getCellCoordinates().getRow() == cellInformation[cellInformation.length-1].getCellCoordinates().getRow())
			return true;
		else
			return false;
	}
	
	public static ContentValueType identifyValueType(String strValue) {
		String value = strValue.replace(',', '.');
		ContentValueType type = ContentValueType.OTHER;
		if (value.isEmpty())
			type = ContentValueType.EMPTY;
		else {
			try {
				new Integer(value);
				type = ContentValueType.STRING_NUMBER;
			} catch (NumberFormatException ex) {}
		}
		
		if (type == ContentValueType.OTHER) {
			try {
				new Float(value);
				type = ContentValueType.FLOAT;
			} catch (NumberFormatException ex) {}
		}
		if (type == ContentValueType.OTHER) 
			type = ContentValueType.STRING_NUMBER;
		
		return type;
	}
	
	// The content is at best interpreted as a string if it is not a number and contains 75 % letters
	public static boolean isString(String strValue) {
		return isString(strValue, true);
	}
	
	public static boolean isString(String strValue, boolean mostlyLetters) {
		String value = strValue.replace(',', '.');
		
		if (value.isEmpty())
			return false;
	
		try {
			new Integer(value);
			return false;
		} catch (NumberFormatException ex) {}
			
		try {
			new Float(value);
			return false;
		} catch (NumberFormatException ex) {}
		
		if (mostlyLetters) {
			int letters = 0;
			for (int i = 0; i < strValue.length(); i++)
				if (Character.isLetter(strValue.charAt(i)) || Character.isWhitespace(strValue.charAt(i)))
					letters++;
			if ( new Float(letters/ new Float(strValue.length())) >= 0.75f)
				return true;
			else
				return false;
		} else
			return true;
		
	}
	
	public static List<Integer> convertLegendsToIds(List<Legend> legends) {
		List<Integer> ids = new ArrayList<Integer>();
		for (Legend legend : legends)
			ids.add(legend.getId());
		return ids;
	}
	
	public static List<Integer> convertFBsToIds(List<FunctionalBlock> fbs) {
		List<Integer> ids = new ArrayList<Integer>();
		for (FunctionalBlock fb : fbs)
			ids.add(fb.getId());
		return ids;
	}
	
	public static List<Legend> convertIdsToLegends(List<Integer> ids, AbstractSsModel asm) {
		List<Legend> legends = new ArrayList<Legend>();
		for (Integer id : ids)
			legends.add(asm.getLegendById(id));
		return legends;
	}
	
	public static List<FunctionalBlock> convertIdsToFBs(List<Integer> ids, AbstractSsModel asm) {
		List<FunctionalBlock> fbs = new ArrayList<FunctionalBlock>();
		for (Integer id : ids)
			fbs.add(asm.getFBById(id));
		return fbs;
	}
	

}
