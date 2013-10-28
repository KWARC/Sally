package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.AxiomVariableObject;
import info.kwarc.sally.spreadsheet3.ontology.DataTypeObject;
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
	
	public static void createCompeteSpecification(Manager manager, FormalSpreadsheet spreadsheet) {
		
	}
	
	public static DataTypeSpec getDataTypeSpecification(Manager manager, List<DataSymbolInformation> dataSymbols) {
		List<String> specification = new ArrayList<String>();
		Map<String, String> viToZ3String = new HashMap<String,String>();

		/*
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
			function = function + ")\n)";
			specification.add(function);
		}
		return new DataTypeSpec(specification, idToSymbol);*/
		
		// Generating symbols
		String objectDefinition = "(declare-datatypes () ((Object ";
		
		for (int id = 0; id < dataSymbols.size(); id++) {
			objectDefinition += "Sym-" + id + " ";
			dataSymbols.get(id).setSymbolID(id);
		}
		objectDefinition += ")))";
		specification.add(objectDefinition);
		
		// Generating datatype String
		for (DataSymbolInformation symbol : dataSymbols) {
			if (manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String) {
				viToZ3String.put(symbol.getContent(), toZ3Value(ml2Z3(symbol.getContent(), mathML2Z3XLSTTypes)));
			}
		}
		if (!viToZ3String.values().isEmpty()) {
			String stringDefinition = "(declare-datatypes () ((String ";
			for (String s : viToZ3String.values())
				stringDefinition += s + " ";
			stringDefinition += ")))";
			specification.add(stringDefinition);
		}
		
		// Declare value functions
		specification.add("(declare-fun value-String (Object) String)");
		specification.add("(declare-fun value-Real (Object) Real)");
		specification.add("(declare-fun value-Int (Object) Int)");
		specification.add("(declare-fun value-Bool (Object) Bool)");
		
		// Generate type checking functions
		Map<String, List<Integer>> dataTypes = new HashMap<String, List<Integer>>();
		for (DataSymbolInformation symbol : dataSymbols) {
			List<Integer> idList;
			if (dataTypes.containsKey(symbol.getOntologyType()))
				idList = dataTypes.get(symbol.getOntologyType());
			else {
				idList = new ArrayList<Integer>();
				dataTypes.put(symbol.getOntologyType(), idList);
			}
			idList.add(symbol.getSymbolID());
		}
		for (String dataType : dataTypes.keySet()) {
			String typeFunctionDefinition = "(define-fun is-" + uriToIdentifier(dataType) + " ((x Object)) Bool \n (or ";
			for (Integer id : dataTypes.get(dataType))
				typeFunctionDefinition += "(= x Sym-" + id + ") ";
			typeFunctionDefinition += ")\n)";
			specification.add(typeFunctionDefinition);
		}
		
		// Asserting values to symbols
		for (DataSymbolInformation symbol : dataSymbols) {
			String value =  ml2Z3(symbol.getContent(),mathML2Z3XLSTFunctions);
			if (manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String)
				value = toZ3Value(value);
			if (!value.isEmpty())
				specification.add("(assert (= value-" + manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType().name() + " Sym-" + symbol.getSymbolID() + ") " + value + "))");
		}
		return new DataTypeSpec(specification, viToZ3String);

	}
		
	public static List<String> createFunctionDeclarations(List<FunctionObject> functions, Manager manager) {
		List<String> declarations = new ArrayList<String>();
		for (FunctionObject function : functions) {
			if (function.getMLDefinition().isEmpty()) {
				declarations.add(getFunctionDeclaration(function, manager));
			}
		}
		return declarations;
	}
	
	public static List<String> createFunctionDefinitions(List<FunctionObject> functions, Manager manager, Map<String, String> viToZ3String) {
		List<String> definitions = new ArrayList<String>();
		for (FunctionObject function : functions) {
			if (!function.getMLDefinition().isEmpty()) {
				definitions.add(getFunctionDefinition(function, manager, viToZ3String));
			}
		}
		return definitions;
	}
	
	public static String getAxiom(AxiomObject axiom, Map<String, String> identifierToSymbol) {
		String axiomSpec = "(assert ";
		
		Map<String, String> varType = new HashMap<String,String>();
		List<AxiomVariableObject> allQuantVars = new ArrayList<AxiomVariableObject>();
		List<AxiomVariableObject> existQuantVars = new ArrayList<AxiomVariableObject>();
		for (AxiomVariableObject var : axiom.getVariables()) {
			if (var.getQuantorType() == AxiomVariableObject.QuantorType.All)
				allQuantVars.add(var);
			else
				existQuantVars.add(var);
		}
		if (!allQuantVars.isEmpty()) {
			axiomSpec += "(forall (";
			for (AxiomVariableObject var : allQuantVars) {
				if (isStandardType(var.getType()))
					axiomSpec += "(" + var.getName() + " " + uriToIdentifier(var.getType()) + ")";
				else {
					axiomSpec += "(" + var.getName() + " Object)";
					varType.put(var.getName(), var.getType());
				}
			}
			axiomSpec += "\n";
		}
		if (!existQuantVars.isEmpty()) {
			axiomSpec += "(exists (";
			for (AxiomVariableObject var : existQuantVars) {
				if (isStandardType(var.getType()))
					axiomSpec += "(" + var.getName() + " " + uriToIdentifier(var.getType()) + ")";
				else {
					axiomSpec += "(" + var.getName() + " Object)";
					varType.put(var.getName(), var.getType());
				}
			}
			axiomSpec += "\n";
		}
		axiomSpec += "=>\n  (and\n";
		for (String v : varType.keySet())
			axiomSpec += "     (is-" + uriToIdentifier(varType.get(v)) + " " + v + ")\n";
		
		if (!axiom.getVarConditions().isEmpty())
			axiomSpec += mathML2Z3(axiom.getVarConditions(), mathML2Z3XLSTFunctions, identifierToSymbol) + "\n";
		axiomSpec += "  )\n  " + mathML2Z3(axiom.getMLConstrain(), mathML2Z3XLSTFunctions, identifierToSymbol) + ")\n";
		
		if (!existQuantVars.isEmpty())
			axiomSpec += ")";
		
		if (!allQuantVars.isEmpty())
			axiomSpec += ")";

		return axiomSpec + ")";
	}
	
	private static String getFunctionDeclaration(FunctionObject function, Manager manager) {
		String funcDef = "(declare-fun " + uriToIdentifier(function.getUri()) + " (";
		for (String argType : function.getArgumentTypes()) {
			funcDef = funcDef +  manager.getOntologyInterface().getDataTypeObject(argType).getBasicType().name() + " ";
		}
		return funcDef + ") " + manager.getOntologyInterface().getDataTypeObject(function.getResultType()).getBasicType().name() + ")";
	}

	// TODO: 
	// - All functions on standard Datatypes. Mapping uri -> Z3 Type (Ontology)
	// - Replace Ontology Object by its value.
	/*private static String getFunctionDefinition(FunctionObject function, Map<String, String> identifierToSymbol, Map<String, DataTypeObject> dataTypeObjects) {
		String funcDef = "(define-fun " + Util.getCDFromURI(function.getUri()) + "~" + Util.getSymbolFromURI(function.getUri()) + " (";
		Map<String, String> varType = new HashMap<String,String>();
		for (int i = 0; i < function.getArgumentTypes().size(); i++) {
			funcDef = funcDef + "(" + mathML2Z3(function.getBuilderML().getVIVaribale(i), mathML2Z3XLSTFunctions, identifierToSymbol);
			/*if (isStandardType(function.getArgumentTypes().get(i)) )
				funcDef = funcDef + uriToIdentifier(function.getArgumentTypes().get(i)) + ")";
			else {
				funcDef = funcDef + "Object )";
				varType.put(function.getBuilderML().getVIVaribale(i), uriToIdentifier(function.getArgumentTypes().get(i)));
			}* /
			funcDef = funcDef + dataTypeObjects.get(function.getArgumentTypes().get(i)) + ")";
		}
		funcDef =  funcDef + ") " + dataTypeObjects.get(function.getResultType()) + "\n";
		if (!varType.isEmpty()) {
			funcDef = funcDef + "(ite (and\n";
			for (String var : varType.keySet())
				funcDef = funcDef + "(is-" + varType.get(var) + " " +  mathML2Z3(var, mathML2Z3XLSTFunctions, identifierToSymbol) + ")\n";
			funcDef = funcDef + ")";
			funcDef = funcDef + mathML2Z3(function.getMLDefinition(), mathML2Z3XLSTFunctions, identifierToSymbol);
			funcDef = funcDef + BADTYPE + "\n))";
		} else
			funcDef = funcDef + mathML2Z3(function.getMLDefinition(), mathML2Z3XLSTFunctions, identifierToSymbol) + "\n)";
		
		return funcDef;
	}*/
	
	private static String getFunctionDefinition(FunctionObject function, Manager manager, Map<String, String> viToZ3String) {
		String funcDef = "(define-fun " + uriToIdentifier(function.getUri()) + " (";
		for (int i = 0; i < function.getArgumentTypes().size(); i++) 
			funcDef += "(x" + i + " " + manager.getOntologyInterface().getDataTypeObject(function.getArgumentTypes().get(i)).getBasicType().name() + ")";
		funcDef += ") " +  manager.getOntologyInterface().getDataTypeObject(function.getResultType()).getBasicType().name() + "\n";
		
		// Replace identifiers with Z3 valid name
		String mlDef = function.getMLDefinition();
		for (String vi : viToZ3String.keySet())
			mlDef = mlDef.replaceAll(vi, viToZ3String.get(vi));
		
		funcDef = funcDef + ml2Z3(mlDef, mathML2Z3XLSTFunctions);
		funcDef += "\n)";
		return funcDef;
	}
	
	private static String mathML2Z3(String expression, String template, Map<String, String> identifierToSymbol) {
		//logger.info("Try to transform: " + expression);
		
		// Map Identifier to symbols
		for (String identifier : identifierToSymbol.keySet())
			expression = expression.replaceAll(identifier, identifierToSymbol.get(identifier));
		
		return ml2Z3(expression, template);
		
		/*String resultStr = "";
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
		//logger.info("  ...transformed.");
		return resultStr;*/
	}
	
	private static String ml2Z3(String expression, String template) {
		//logger.info("Try to transform: " + expression);
			
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
		//logger.info("  ...transformed.");
		return resultStr;
	}
		
	private static String uriToIdentifier(String uri) {
		if (Util.isOMDocUri(uri)) {
			if (isStandardType(uri))
				return Util.getSymbolFromURI(uri);
			else
				return Util.getCDFromURI(uri) + "~" + Util.getSymbolFromURI(uri);
		} else
			return "";
	}
	
	private static Boolean isStandardType(String uri) {
		String[] mathMLDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
		boolean isMathMLDT = false;
		for (String dt : mathMLDataTypes)
			if (dt.equals(uri) )
				isMathMLDT = true;
		return isMathMLDT;
	}
	
	private static String toZ3Value(String s) {
		return s.trim().replaceAll(" ", "-");
	}

}
