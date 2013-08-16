package info.kwarc.sally.spreadsheet2;


import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class Util {

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
	
	public static List<CellSpaceInformation> expandRange(CellSpaceInformation start, CellSpaceInformation end) {
		List<CellSpaceInformation> allPositions = new ArrayList<CellSpaceInformation>();
		if (start.getWorksheet().equals(end.getWorksheet())) {
			int startRow = java.lang.Math.min(start.getRow(), end.getRow());
			int endRow = java.lang.Math.max(start.getRow(), end.getRow());
			int startCol = java.lang.Math.min(start.getColumn(), end.getColumn());
			int endCol = java.lang.Math.max(start.getColumn(), end.getColumn());
			for (int i = startRow; i <= endRow; i++) {
				for (int j = startCol; j <= endCol; j++) {
					allPositions.add(new CellSpaceInformation(start.getWorksheet(),i,j));
				}
			}
		}
		return allPositions;
	}
	
	public static List<Integer> convertBlocksToIDs(List<Block> blocks) {
		List<Integer> ids = new ArrayList<Integer>();
		for (Block b : blocks)
			ids.add(b.getId());
		return ids;
	}
	

	
}
