package info.kwarc.sally.spreadsheet3;


import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.model.RangeInformation;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Util {
	
	// The URIs for resources have the form: http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costsCD?sax-costsSym
	static Pattern omdocUriPattern = Pattern.compile("(\\S+?)\\?(\\S+?)\\?(\\S+?)");
	
	static Pattern cellAddressPattern = Pattern.compile("([A-Z]+)([0-9]+)");
	static Pattern rangeAddressPattern = Pattern.compile("(.+)!([A-Z]+)([0-9]+):([A-Z]+)([0-9]+)");
	
	/**
	 * Converts ranges like Sheet1!C4:F10 to structured range information
	 * @param position A range position with sheetname
	 * @return 
	 */
	public static RangeInformation convertRangeAddress(String position)  {
		Matcher m = rangeAddressPattern.matcher(position);

		if (m.find()) {
			return new RangeInformation(m.group(1), convertRangeCharacter(m.group(2)), Integer.parseInt(m.group(3))-1, convertRangeCharacter(m.group(4)), Integer.parseInt(m.group(5))-1);
		} else
			return null;	
	}
	
	/**
	 * Converts a Excel cell reference like C4 to structured cell information.
	 * @param position A cell position without sheetname
	 * @return
	 */
	public static CellSpaceInformation convertCellPosition(String position)  {
		Matcher m = cellAddressPattern.matcher(position);

		if (m.find()) {
			return new CellSpaceInformation(Integer.parseInt(m.group(2))-1, convertRangeCharacter(m.group(1)));
		} else
			return null;	
	}
	
	/**
	 * Converts range characters (e.g. AC) to a column index.
	 * @param A string of range characters
	 * @return
	 */
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
	
	/**
	 * Converts a column index to a string representation 
	 * @param index The index of a column. 0 is mapped to A
	 * @return
	 */
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
	
	/**
	 * Identifies the content type of a string (empty, float, string, number or other).
	 * @param strValue The string that should be analyzed
	 * @return
	 */
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
	
	/**
	 * Test if the content of a string is at best interpreted as a text-string ( contains >75 % letters).
	 * @param strValue The string to analyse
	 * @return
	 */
	public static boolean isString(String strValue) {
		return isString(strValue, true);
	}
	
	/**
	 * Test if the content of a string is at best interpreted as a text-string ( contains >75 % letters or is not a number).
	 * @param strValue The string to analyse
	 * @param mostlyLetters true: String if >75% letters ; false String if not empty and no number
	 * @return
	 */
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
	
	/**
	 * Returns a list of all cell positions between start and end (A3,B4 -> A3,A4,B3,B4).
	 * @param start The start position
	 * @param end The end position
	 * @return
	 */
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
	
	/**
	 * Convert a list of block to a list of block ids.
	 * @param blocks
	 * @return
	 */
	public static List<Integer> convertBlocksToIDs(List<Block> blocks) {
		List<Integer> ids = new ArrayList<Integer>();
		for (Block b : blocks)
			ids.add(b.getId());
		return ids;
	}
	
	/**
	 * Convert a list of block ids to a list of blocks.
	 * @param ids List of block ids.
	 * @param m A manager that contains the blocks.
	 * @return
	 */
	public static List<Block> convertIDsToBlocks(List<Integer> ids, ModelManager m) {
		List<Block> blocks = new ArrayList<Block>();
		for (Integer id : ids)
			blocks.add(m.getBlockByID(id));
		return blocks;
	}
	
	/**
	 * Convert a list of relations to a list of relation ids.
	 * @param relations
	 * @return
	 */
	public static List<Integer> convertRelationsToIDs(List<Relation> relations) {
		List<Integer> ids = new ArrayList<Integer>();
		for (Relation r : relations)
			ids.add(r.getId());
		return ids;
	}
	
	/**
	 * Try to antiunify a list of formulae.
	 * @see testAntiunifyMathMLFormulae in UtilTest.java
	 * @param formulae A list of formulae in OpenMath/MathML
	 * @param domainValues A list of domain values. For each function a list of domain values is necessary
	 * @param ml A BuilderML instance is necessary to parse OpenMath or MathML. 
	 * @return An empty string if the formulae could not be antiunified or otherwise their antiunification. 
	 */
	public static String antiunifyMathMLFormulae(List<String> formulae, List<List<String>> domainValues, BuilderML ml) {
		if (formulae.size() != domainValues.size())
			return "";
		
		String antiunification = "";
		boolean conflict = false;
			
		for (int i = 0; (i < formulae.size()) && !conflict; i++) {
			String formula = formulae.get(i);
			
			Map<String, String> replacements = new HashMap<String, String>();
			for (int j = 0; j < domainValues.get(i).size(); j++) 
				replacements.put(domainValues.get(i).get(j), ml.getVIVaribale(j));
			
			for (String semObj : replacements.keySet())
				formula = formula.replace(semObj, replacements.get(semObj));
			
			if (antiunification.isEmpty())
				antiunification = formula;
			else if (!antiunification.equals(formula))
				conflict = true;
		}
		if (!conflict)
			return antiunification;
		else
			return "";
	}
	
	/**
	 * Returns information about constant arguments in a list of domain values.
	 * In example (1984 , Revenues) and (1984, Material Costs) have the constant argument 1984 in the first argument.
	 * @param domainValues A list of domain values.
	 * @return
	 */
	public static Map<Integer, String> getConstantArguments(List<List<String>> domainValues) {
		Map<Integer, String> arguments = new HashMap<Integer,String>();
		
		for (int j = 0; j < domainValues.get(0).size(); j++) {
			boolean equal = true;
			String firstValue = domainValues.get(0).get(j);
			for (int i = 1; i < domainValues.size(); i++) {
				if (!firstValue.equals(domainValues.get(i).get(j)))
					equal = false;
			}
			if (equal)
				arguments.put(j, firstValue);
		}
		
		return arguments;
	}
	
	/**
	 * Tag a string with a start and end tag for MathML or OpenMath.
	 */
	public static String tagAsMathObject(String s, BuilderML ml) {
		return ml.getMathTagBegin() + "\n" + s + ml.getMathTagEnd() + "\n";
	}
	
	/**
	 * Remove start and end tag for MathML or OpenMath from a string. 
	 */
	public static String untagMathObject(String s, BuilderML ml) {
		return s.replace(ml.getMathTagBegin() + "\r\n", "")
				.replace(ml.getMathTagBegin() + "\n", "")
				.replace(ml.getMathTagEnd() + "\r\n","")
				.replace(ml.getMathTagEnd() + "\n","")
				.replace(ml.getMathTagEnd(), "");
	}
	
	/**
	 * Is the string a valid uri for an Omdoc resource
	 * @param uri the string that contains the URI.
	 * @return
	 */
	public static boolean isOMDocUri(String uri) {
		return omdocUriPattern.matcher(uri).matches();
	}
	
	/**
	 * Extract the content dictionary from an URI.
	 * http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costsCD?sax-costsSym -> sax-costsCD
	 * @param uri
	 * @return
	 */
	public static String getCDFromURI(String uri) {
		Matcher matcher = omdocUriPattern.matcher(uri);
		if (matcher.matches())
			return matcher.group(2);
		else
			return "";
	}
	
	/**
	 * Extract the symbol name from an URI.
	 * http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costsCD?sax-costsSym -> sax-costsSym
	 * @param uri
	 * @return
	 */
	public static String getSymbolFromURI(String uri) {
		Matcher matcher = omdocUriPattern.matcher(uri);
		if (matcher.matches())
			return matcher.group(3);
		else
			return "";
	}
	
	/**
	 * Replaces all URIs of Omdoc resource by identifiers (ContentDictionary~Symbol)
	 * @param data A string that can contain several URIs.
	 * @return
	 */
	public static String replaceURIsWithIdentifiers(String data) {
		Matcher matcher = omdocUriPattern.matcher(data);
		String result = "";
		int lastIndex = 0;
		while (matcher.find()) {
			result = result + data.substring(lastIndex, matcher.start());
			result = result + getCDFromURI(matcher.group()) + "~" + getSymbolFromURI(matcher.group());
			lastIndex = matcher.end();
		}
		result = result + data.substring(lastIndex);
		return result;
	}
	
}
