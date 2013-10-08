package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.w3c.dom.Document;
import org.xml.sax.SAXException;

public class VerificationSpecificationGenerator {
	
	final static String mathML2Z3XLSTTypes = "src/main/resources/MathML2Z3Types.xsl";
	final static String mathML2Z3XLSTFunctions = "src/main/resources/MathML2Z3Functions.xsl";
	final static String mathML2Z3XLSTAxioms = "src/main/resources/MathML2Z3Axioms.xsl";
	final static Logger logger = LoggerFactory.getLogger(VerificationSpecificationGenerator.class);
	final static String BADTYPE = "(- 99999999)";
	
	
	public static DataTypeSpec getDataTypeSpecification(Map<String, List<String>> dataTypes) {
		/*List<String> allSymbols = new ArrayList<String>();
		
		for (List<String> symbols : dataTypes.values())
			allSymbols.addAll(symbols);
		
		String objectDefinition = "(declare-datatypes () ((Object ";
		for (String symbol : allSymbols)
			objectDefinition = objectDefinition + dtMathML2Z3(symbol) + " ";
		
		objectDefinition = objectDefinition + ")))";
		
		List<String> specification = new ArrayList<String>();
		specification.add(objectDefinition);
		for (String dataTyp : dataTypes.keySet()) {
			String function = "(define-fun is-" + dataTyp +  " ((x Object)) Bool\n" + " (or ";
			for (String symbol : dataTypes.get(dataTyp))
				function = function + "(= x " + dtMathML2Z3(symbol) + ") ";
			function = function + ")\n)\n";
			specification.add(function);
		}
		return specification;*/
		
		List<String> specification = new ArrayList<String>();

		// Generating abstract symbols 
		int maxID = 0;
		Map<String, String> idToSymbol = new HashMap<String, String>();
		Map<String, String> symbolToId = new HashMap<String, String>();
		
		for (List<String> symbols : dataTypes.values()) {
			for (String symbol : symbols) {
				if (!symbolToId.containsKey(symbol)) {
					idToSymbol.put("Sym-" + maxID, symbol);
					symbolToId.put(symbol, "Sym-" + maxID);
					maxID++;
				}
			}
		}
		
		String objectDefinition = "(declare-datatypes () ((Object ";
		for (String id : idToSymbol.keySet())
			objectDefinition = objectDefinition + id +  " ";
		
		objectDefinition = objectDefinition + ")))";
		specification.add(objectDefinition);
		
		// Asserting concrete symbol definitions to abstract symbols
		for (String id : idToSymbol.keySet())
			specification.add("(assert (= " + id + " " + mathML2Z3(idToSymbol.get(id), mathML2Z3XLSTTypes, idToSymbol) + ") )");
		
		for (String dataTyp : dataTypes.keySet()) {
			String function = "(define-fun is-" + Util.getCDFromURI(dataTyp) + "~" + Util.getSymbolFromURI(dataTyp) +  " ((x Object)) Bool\n" + " (or ";
			for (String symbol : dataTypes.get(dataTyp))
				function = function + "(= x " + symbolToId.get(symbol) + ") ";
			function = function + ")\n)\n";
			specification.add(function);
		}
		return new DataTypeSpec(specification, idToSymbol);
		
	}
	
	public static String getFunctionDefinition(FunctionObject function, Map<String, String> identifierToSymbol) {
		String funcDef = "(define-fun " + Util.getCDFromURI(function.getUri()) + "~" + Util.getSymbolFromURI(function.getUri()) + " (";
		Map<String, String> varType = new HashMap<String,String>();
		for (int i = 0; i < function.getArgumentTypes().size(); i++) {
			funcDef = funcDef + "(" + function.getBuilderML().getVIVaribale(i) + " ";
			if (isStandardType(function.getArgumentTypes().get(i)) )
				funcDef = funcDef + uriToIdentifier(function.getArgumentTypes().get(i)) + ")";
			else {
				funcDef = funcDef + "Object )";
				varType.put(function.getBuilderML().getVIVaribale(i), uriToIdentifier(function.getArgumentTypes().get(i)));
			}
		}
		funcDef =  funcDef + ") " + uriToIdentifier(function.getResultType()) + "\n"; 
		if (!varType.isEmpty()) {
			funcDef = funcDef + "(ite (and\n";
			for (String var : varType.keySet())
				funcDef = funcDef + "(is-" + varType.get(var) + " " + var + ")\n";
			funcDef = funcDef + ")\n";
			funcDef = funcDef + mathML2Z3(function.getMLDefinition(), mathML2Z3XLSTFunctions, identifierToSymbol) + "\n";
			funcDef = funcDef + BADTYPE + "\n))\n";
		} else
			funcDef = funcDef + mathML2Z3(function.getMLDefinition(), mathML2Z3XLSTFunctions, identifierToSymbol) + "\n)\n";
		
		return funcDef;
	}
	
	public static String getFunctionDeclaration(String functionName, List<String> arguments, String result) {
		String funcDef = "(declare-fun " + functionName + " (";
		for (String varName : arguments) {
			if (isStandardType(varName))
				funcDef = funcDef +  uriToIdentifier(varName) + " ";
			else
				funcDef = funcDef +  "Object ";
		}
		return funcDef + ") " + uriToIdentifier(result) + ")\n";
	}
	
	public static String getAxiom(String axiom) {
		return "(assert " +  mathML2Z3(axiom, mathML2Z3XLSTAxioms, new HashMap<String, String>()) + ") )";
	}
	
	public static List<String> createFunctionDefinitions(List<FunctionObject> functions, Map<String, String> identifierToSymbol) {
		List<String> definitions = new ArrayList<String>();
		for (FunctionObject function : functions) {
			if (!function.getMLDefinition().isEmpty()) {
				definitions.add(getFunctionDefinition(function, identifierToSymbol));
			}
		}
		return definitions;
	}
	
	public static List<String> createFunctionDeclarations(List<FunctionObject> functions) {
		List<String> declarations = new ArrayList<String>();
		for (FunctionObject function : functions) {
			if (function.getMLDefinition().isEmpty()) {
				declarations.add(getFunctionDeclaration(uriToIdentifier(function.getUri()), function.getArgumentTypes(), function.getResultType()));
			}
		}
		return declarations;
	}
	
	public static String mathML2Z3(String expression, String template, Map<String, String> identifierToSymbol) {
		// Map Identifier to symbols
		for (String identifier : identifierToSymbol.keySet())
			expression = expression.replaceAll(identifier, identifierToSymbol.get(identifier));
		
		String resultStr = "";
		try {
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	        DocumentBuilder builder = factory.newDocumentBuilder();
	        
	        String xmlStatement = "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" + expression + "</math>";
	        Document document = builder.parse(new ByteArrayInputStream(xmlStatement.getBytes()));
	            
	        // Use a Transformer for output
	        TransformerFactory tFactory = TransformerFactory.newInstance();
	        StreamSource stylesource = new StreamSource(template);
	        Transformer transformer = tFactory.newTransformer(stylesource);
 
	        DOMSource source = new DOMSource(document);
	        StreamResult result = new StreamResult(new ByteArrayOutputStream());
	        transformer.transform(source, result);
	        resultStr = result.getOutputStream().toString();
		} catch (ParserConfigurationException e ) {
			logger.error("MathML to Z3 transformation failed. Message: " + e.getMessage());
		} catch (SAXException e) {
			logger.error("MathML to Z3 transformation failed. Message: " + e.getMessage());
		} catch (IOException e) {
			logger.error("MathML to Z3 transformation failed. Message: " + e.getMessage());
		} catch (TransformerConfigurationException e) {
			logger.error("MathML to Z3 transformation failed. Message: " + e.getMessage());
		} catch (TransformerException e) {
			logger.error("MathML to Z3 transformation failed. Message: " + e.getMessage());
		} 
		return resultStr;
	}
	
	public static void createCompeteSpecification(Manager manager, FormalSpreadsheet spreadsheet) {
	
	}
	
	public static String uriToIdentifier(String uri) {
		if (Util.isOMDocUri(uri)) {
			if (isStandardType(uri))
				return Util.getSymbolFromURI(uri);
			else
				return Util.getCDFromURI(uri) + "~" + Util.getSymbolFromURI(uri);
		} else
			return "";
	}
	
	public static Boolean isStandardType(String uri) {
		String[] mathMLDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
		boolean isMathMLDT = false;
		for (String dt : mathMLDataTypes)
			if (dt.equals(uri) )
				isMathMLDT = true;
		return isMathMLDT;
	}

}
