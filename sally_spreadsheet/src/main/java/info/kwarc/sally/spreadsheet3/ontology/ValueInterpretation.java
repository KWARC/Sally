package info.kwarc.sally.spreadsheet3.ontology;

import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ValueInterpretation {
	
	Pattern valuePattern;
	final String patternStr;		// Just necessary for the implementation of equals() and hashCode(), because Pattern does not support those functions.
	final String interpretationTemplate;
	final BuilderML builderML;
	
	
	/**
	 * A value interpretation is the corresponding ontology element (described in MathML) for a value.
	 * @param patternStr A pattern that describes the structure of the value, e.g. #1 which matches the complete value or M#1-#2 to match expressions like M126-a and extracting the parameters "126" and "a".
	 * @param subExpressions Each identifier #id in patternStr can be described by a regular expression, e.g. \d for a digit or \p{Alpha}+ for a non empty text.
	 * @param interpretationTemplate A MathML template that can refer the identifiers from patternstr by rvar, e.g. <apply><csymbol>times</csymbol><ci><rvar num="1"/></ci><ci>1000000</ci></apply>
	 */
	public ValueInterpretation(String patternStr, Map<Integer, String> subExpressions, String interpretationTemplate, BuilderML builderML) {
		// Generating pattern for value parsing
		for (Integer id : subExpressions.keySet()) {
			String escapedSubExpr =  subExpressions.get(id).replace("\\", "\\\\");
			patternStr = patternStr.replaceAll("#"+id, "(" + escapedSubExpr + ")");
		}
		this.valuePattern = Pattern.compile(patternStr);
		this.patternStr = patternStr;
		this.interpretationTemplate = interpretationTemplate;
		this.builderML = builderML;
	}
	
	public ValueInterpretation(sally.ValueInterpretationMsg msg) {
		this.valuePattern = Pattern.compile(msg.getPattern());
		this.patternStr = msg.getPattern();
		this.interpretationTemplate = msg.getInterpretationTemplate();
		if (msg.getBuilderML().getType().equals(sally.BuilderMsg.Type.MathML))
			this.builderML = new BuilderMathML();
		else if (msg.getBuilderML().getType().equals(sally.BuilderMsg.Type.OpenMath))
			this.builderML = new BuilderOpenMath();
		else
			throw new java.lang.IllegalArgumentException("Unknown BuilderML type.");
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime
				* result
				+ ((interpretationTemplate == null) ? 0
						: interpretationTemplate.hashCode());
		result = prime * result
				+ ((patternStr == null) ? 0 : patternStr.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ValueInterpretation other = (ValueInterpretation) obj;
		if (interpretationTemplate == null) {
			if (other.interpretationTemplate != null)
				return false;
		} else if (!interpretationTemplate.equals(other.interpretationTemplate))
			return false;
		if (patternStr == null) {
			if (other.patternStr != null)
				return false;
		} else if (!patternStr.equals(other.patternStr))
			return false;
		return true;
	}

	public Boolean isInterpretable(String value) {
		return valuePattern.matcher(value).matches();
	}

	public String getValueInterpretation(String value) {	
		Matcher matcher = valuePattern.matcher(value);
		
		if (matcher.matches() ) {
			String interpretation = interpretationTemplate;
			for (int i = 1; i <= matcher.groupCount(); i++) {
				interpretation = interpretation.replaceAll(builderML.getVIVaribale(i), matcher.group(i));
			}
			return interpretation;
		} else
			return "";
	}
	
	@Override
	public String toString() {
		return "Pattern: " + valuePattern.toString() + " Template: " + interpretationTemplate;
	}
	
	public sally.ValueInterpretationMsg serialize() {
		sally.ValueInterpretationMsg.Builder msgBuilder = sally.ValueInterpretationMsg.newBuilder();
		msgBuilder.setPattern(valuePattern.toString());
		msgBuilder.setInterpretationTemplate(interpretationTemplate);

		if (builderML instanceof BuilderML)
			msgBuilder.setBuilderML(sally.BuilderMsg.newBuilder().setType(sally.BuilderMsg.Type.MathML).build());
		else if (builderML instanceof BuilderOpenMath)
			msgBuilder.setBuilderML(sally.BuilderMsg.newBuilder().setType(sally.BuilderMsg.Type.OpenMath).build());
		else
			throw new java.lang.InstantiationError("Builder for math makeup is either MathML nor OpenMath.");
		
		return msgBuilder.build();
	}

}
