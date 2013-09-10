package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class VerificationSpecificationGenerator {
	
	public static void getDataTypeSpecification(Map<String, List<String>> dataTypes) {
		List<String> allSymbols = new ArrayList<String>();
		
		for (List<String> symbols : dataTypes.values())
			allSymbols.addAll(symbols);
		
		String objectDefinition = "(declare-datatypes () ((Object ";
		for (String symbol : allSymbols)
			objectDefinition = objectDefinition + symbol + " ";
		
		objectDefinition = objectDefinition + ")))";
		
		List<String> dataTypeFunctions = new ArrayList<String>();
		for (String dataTyp : dataTypes.keySet()) {
			String function = "(define-fun is-" + dataTyp +  " ((x Object)) Bool\n" + " (or ";
			for (String symbol : dataTypes.get(dataTyp))
				function = function + "(= x " + symbol + ") ";
			function = function + ")\n)\n";
			dataTypeFunctions.add(function);
		}
		
		
	}
	
	public static void getFunctionDefinition(String functionName, Map<String, String> arguments, String result, String definition) {
		String funcDef = "(define-fun " + functionName + " (";
		for (String varName : arguments.keySet())
			funcDef = funcDef + "(" + varName + " " + arguments.get(varName) + ")";
		funcDef = funcDef + ") " + result + "\n";
		funcDef = funcDef + definition;
		funcDef = funcDef + ")\n";
	}
	
	public static void getFunctionDeclaration(String functionName, List<String> arguments, String result) {
		String funcDef = "(declare-fun " + functionName + " (";
		for (String varName : arguments)
			funcDef = funcDef +  varName + " ";
		funcDef = funcDef + ") " + result + ")\n";
	}
	
	public static void createFunctionDefinitions(List<OntologyFunctionObject> functions) {
		for (OntologyFunctionObject function : functions) {
			if (!function.getMathMLDefinition().isEmpty()) {
				
			}
		}
	}
	
	

}
