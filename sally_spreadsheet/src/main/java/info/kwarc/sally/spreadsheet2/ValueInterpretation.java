package info.kwarc.sally.spreadsheet2;

import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

class ValueInterpretation {
	
	Pattern valuePattern;
	final String interpretationTemplate;
	
	
	/**
	 * A value interpretation is the corresponding ontology element (described in MathML) for a value.
	 * @param patternStr A pattern that describes the structure of the value, e.g. #1 which matches the complete value or M#1-#2 to match expressions like M126-a and extracting the parameters "126" and "a".
	 * @param subExpressions Each identifier #id in patternStr can be described by a regular expression, e.g. \d for a digit or \p{Alpha}+ for a non empty text.
	 * @param interpretationTemplate A MathML template that can refer the identifiers from patternstr by rvar, e.g. <apply><csymbol>times</csymbol><ci><rvar num="1"/></ci><ci>1000000</ci></apply>
	 */
	public ValueInterpretation(String patternStr, Map<Integer, String> subExpressions, String interpretationTemplate) {
		// Generating pattern for value parsing
		for (Integer id : subExpressions.keySet()) {
			String escapedSubExpr =  subExpressions.get(id).replace("\\", "\\\\");
			patternStr = patternStr.replaceAll("#"+id, "(" + escapedSubExpr + ")");
		}
		this.valuePattern = Pattern.compile(patternStr);
		this.interpretationTemplate = interpretationTemplate;
	}
	
	public Boolean isInterpretable(String value) {
		return valuePattern.matcher(value).matches();
	}
	
	public String getValueInterpretation(String value) {	
		Matcher matcher = valuePattern.matcher(value);
		
		if (matcher.matches()) {
			String interpretation = interpretationTemplate;
			for (int i = 1; i <= matcher.groupCount(); i++) {
				interpretation = interpretationTemplate.replaceAll("<rvar num=\"" + i + "\"/>", matcher.group(i));
			}
			return interpretation;
		} else
			return "";
	}
	
	@Override
	public String toString() {
		return "Pattern: " + valuePattern.toString() + " Template: " + interpretationTemplate;
	}

}
