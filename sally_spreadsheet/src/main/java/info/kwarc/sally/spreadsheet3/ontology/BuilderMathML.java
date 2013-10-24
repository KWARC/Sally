package info.kwarc.sally.spreadsheet3.ontology;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class BuilderMathML extends BuilderML {
	
	Pattern forAllPattern = Pattern.compile("<apply><forall/>((<bvar><ci>.+?</ci></bvar>)+)<condition>(.+?)</condition>(.*)</apply>");
	Pattern existsPattern = Pattern.compile("<apply><exists/>((<bvar><ci>.+?</ci></bvar>)+)<condition>(.+?)</condition>(.*)</apply>");
	Pattern variablePattern = Pattern.compile("<bvar><ci>(.+?)</ci></bvar>");
	Pattern inPattern = Pattern.compile("<apply><in/><ci>(.+?)</ci><ci>(.+?)</ci></apply>");
	
	@Override
	public String getVIVaribale(int i) {
		return "<rvar num=\"" + i + "\"/>";
	}

	@Override
	public String getIdentifier(String s) {
		return "<ci>" + s + "</ci>";
	}

	@Override
	public String getMathTagBegin() {
		return "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">";
	}
	
	@Override
	public String getMathTagEnd() {
		return "</math>";
	}
	
	@Override
	public String getOperatorApplication(String cd, String symbol) {
		return "<apply>\n<csymbol cd=\"" + cd + "\">" + symbol + "</csymbol>";
	}

	@Override
	public String getApplicationEnd() {
		return "</apply>";
	}
	
	@Override
	public AxiomObject parseMLAxiom(String axiom) {
		// axiom = axiom.replaceAll("\\p{Space}", "");

		AxiomObject partialParsed = extractVariables(axiom, forAllPattern);

		AxiomObject parsed = extractVariables(partialParsed.getMLConstrain(), existsPattern);
		
		List<AxiomVariableObject> variables = new ArrayList<AxiomVariableObject>();
		String allQuantVarConditions = "";
		String existQuantVarConditions = "";
		String constrain = "";
		if (partialParsed != null) {
			allQuantVarConditions = reduceConditions(partialParsed.getVarConditions());
			variables.addAll(partialParsed.getVariables());
			constrain = partialParsed.getMLConstrain();
		}
			
		if (parsed != null) {
			existQuantVarConditions = reduceConditions(parsed.getVarConditions());
			variables.addAll(parsed.getVariables());
			constrain = parsed.getMLConstrain();
		}
			
		String varConditions = allQuantVarConditions + existQuantVarConditions;
		
		return new AxiomObject(variables, varConditions, constrain);
	}
	
	private AxiomObject extractVariables(String axiom, Pattern pattern) {
		List<AxiomVariableObject> axiomVariables = new ArrayList<AxiomVariableObject>();
		Map<String, AxiomVariableObject> varMapping = new HashMap<String, AxiomVariableObject>();
		
		// Extracting statement
		Matcher matcher = pattern.matcher(axiom); 
		if (matcher.matches()) {
			String varStatement = matcher.group(1).replaceAll("\\p{Space}", "");
			Matcher varMatcher = variablePattern.matcher(varStatement);
			while (varMatcher.find()) {
				AxiomVariableObject var = new AxiomVariableObject(AxiomVariableObject.QuantorType.All, varMatcher.group(1).trim());
				axiomVariables.add(var);
				varMapping.put(var.getName(), var);
			}
			
			String conditionStatement = matcher.group(3);
			
			// Extracting variable types
			Matcher inMatcher = inPattern.matcher(conditionStatement); 
			while (inMatcher.find()) {
				String varName = inMatcher.group(1).trim();
				String type = inMatcher.group(2);
				AxiomVariableObject var = varMapping.get(varName);
				if (var != null)
					var.setType(type);
				else
					throw new java.lang.IllegalArgumentException("Domain binding for unquantified variable: " + varName);
			}
			conditionStatement = conditionStatement.replaceAll(inPattern.pattern(), "");
			return new AxiomObject(axiomVariables, conditionStatement, matcher.group(4));
		} else {
			return null;
		}
	}
	
	private String reduceConditions(String str) {
		if (str.startsWith("<apply><and/>")) {
				str = str.substring(13,str.length());
				str = str.substring(0, str.length()-8);
		}
		return str;
	}

}
