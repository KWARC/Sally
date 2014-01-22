package info.kwarc.sally.spreadsheet3.extraction;


import info.kwarc.sally.spreadsheet3.ContentValueType;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;

import java.text.DecimalFormat;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.poi.ss.usermodel.Cell;


public class Util {
	
	
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
		String value = strValue.replace(',', '.');
		
		if (value.isEmpty())
			return false;
		else {
			try {
				new Integer(value);
				return false;
			} catch (NumberFormatException ex) {}
		}
		
		try {
			new Float(value);
			return false;
		} catch (NumberFormatException ex) {}
		
		int letters = 0;
		for (int i = 0; i < strValue.length(); i++)
			if (Character.isLetter(strValue.charAt(i)) || Character.isWhitespace(strValue.charAt(i)))
				letters++;
		if ( new Float(letters/ new Float(strValue.length())) >= 0.75f)
			return true;
		else
			return false;
	}
	
	public static CellTypeContent getCellContent(Cell cell) {
		CellTypeContent content = null;
		if (cell == null)
			content = new CellTypeContent(Cell.CELL_TYPE_BLANK, "", "");
		else {
			switch (cell.getCellType()) {
			case Cell.CELL_TYPE_STRING:
				content = new CellTypeContent(Cell.CELL_TYPE_STRING, cell.getStringCellValue(), "");
				break;
			case Cell.CELL_TYPE_NUMERIC:
				String numContent =  new Double(cell.getNumericCellValue()).toString();
				if (numContent.endsWith(".0"))
					numContent = numContent.substring(0, numContent.length()-2);
				content = new CellTypeContent(Cell.CELL_TYPE_NUMERIC, numContent, "");
				
				break;
			case Cell.CELL_TYPE_BOOLEAN:
				content = new CellTypeContent(Cell.CELL_TYPE_BOOLEAN, new Boolean(cell.getBooleanCellValue()).toString(), "");
				break;
			case Cell.CELL_TYPE_FORMULA:
				content = Util.getStringFromFormulaCell(cell);
				break;
			}
		}
		return content;
	}
	
	public static CellTypeContent getStringFromFormulaCell(Cell cell) {
		String value = "";
		int cellType = 0;
		
		
		try {
			value = cell.getStringCellValue();
			cellType = Cell.CELL_TYPE_STRING;
		} catch (java.lang.IllegalStateException e) {
			
		} catch (java.lang.NullPointerException e) {}
		try {
			value = new Boolean(cell.getBooleanCellValue()).toString();
			cellType = Cell.CELL_TYPE_BOOLEAN;
		} catch (java.lang.IllegalStateException e) {
			
		} catch (java.lang.NullPointerException e) {}
		try {
			value = cell.getDateCellValue().toString();
			cellType = Cell.CELL_TYPE_STRING;		// Date is not a valid type in Apache POI.
		} catch (java.lang.IllegalStateException e) {
			
		} catch (java.lang.NullPointerException e) {}
		try {
			value = new Byte(cell.getErrorCellValue()).toString();
			cellType = Cell.CELL_TYPE_ERROR;
		} catch (java.lang.IllegalStateException e) {
			
		} catch (java.lang.NullPointerException e) {}
		try {
			double d = cell.getNumericCellValue();
			value = Util.getRoundedValue(d);
			cellType = Cell.CELL_TYPE_NUMERIC;
		} catch (java.lang.IllegalStateException e) {
			
		} catch (java.lang.NullPointerException e) {}
		
		return new CellTypeContent(cellType, value, cell.getCellFormula());
	}
	
	private static String getRoundedValue(double d) {
		DecimalFormat f = new DecimalFormat();
		f.setDecimalSeparatorAlwaysShown(false);
		String formatPattern = "#0.0";
		String valStr = new Double(d).toString();
		boolean found = false;
		for (int i = valStr.indexOf(".") +1; (i < valStr.length()) && !found; i++) {
			f.applyPattern(formatPattern);
			String rounded = f.format(d);
			rounded = rounded.replaceAll(",", ".");
			if (Math.abs(Double.parseDouble(rounded) - d ) < 0.0001 )
				found = true;
			else
				formatPattern = formatPattern + "0";
		}
		return new DecimalFormat(formatPattern).format(d);
	}

}
