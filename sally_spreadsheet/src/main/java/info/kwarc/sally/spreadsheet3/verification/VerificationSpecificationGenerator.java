package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
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
	
	public static List<String> createCompeteSpecification(Manager manager, FormalSpreadsheet spreadsheet) {
		List<String> specification = new ArrayList<String>();
		
		// Datatypes
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());
		}
		List<DataSymbolInformation> dataSym = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		
		// Specification of symbols, axioms and functions
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllBasicFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllBasicFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym).getSpecification() );
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllDomainFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllDomainFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSym));
		
		for (AxiomObject axiom : manager.getOntologyInterface().getAxioms())
			specification.add(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym));
		
		specification.add("(check-sat)\n");
		
		// Checking cp-similar blocks
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML());
		
		for (CPSimilarBlockData cpBlock : cpBlocks) {
			specification.add("(push)\n");
			specification.add( VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym));
			specification.add("(check-sat)\n");
			specification.add("(pop)\n");
		}
		
		return specification;
	
	}
	
	public static String getObjectSymbolSpecification(List<DataSymbolInformation> dataSymbols) {
		// Generating symbols
		String objectDefinition = "(declare-datatypes () ((Object ";
				
		for (DataSymbolInformation dataSymbol :  dataSymbols) 
			objectDefinition += "Sym-" + dataSymbol.getSymbolID() + " ";
			
		return (objectDefinition + ")))");
		
		
	}
	
	public static DataTypeSpec getDataTypeSpecification(Manager manager, List<DataSymbolInformation> dataSymbols) {
		List<String> specification = new ArrayList<String>();
		Map<String, String> viToZ3String = new HashMap<String,String>();
		
		/*
		// Generating symbols
		String objectDefinition = "(declare-datatypes () ((Object ";
		
		for (DataSymbolInformation dataSymbol :  dataSymbols) 
			objectDefinition += "Sym-" + dataSymbol.getSymbolID() + " ";
	
		objectDefinition += ")))";
		specification.add(objectDefinition);
		*/
		
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
				specification.add("(assert (= (value-" + manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType().name() + " Sym-" + symbol.getSymbolID() + ") " + value + "))");
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
	
	//public static List<String> createFunctionDefinitions(List<FunctionObject> functions, Manager manager, Map<String, String> viToZ3String) {
	public static List<String> createFunctionDefinitions(List<FunctionObject> functions, Manager manager, List<DataSymbolInformation> dataSymbols) {
		List<String> definitions = new ArrayList<String>();
		for (FunctionObject function : functions) {
			if (!function.getMLDefinition().isEmpty()) {
				definitions.add(getFunctionDefinition(function, manager, dataSymbols));
			}
		}
		return definitions;
	}
	
	public static List<String> createFunctionSymbolAssertions(Manager manager, List<DataSymbolInformation> dataSymbols) {
		List<String> specifications = new ArrayList<String>();
		
		Map<CellSpaceInformation, DataSymbolInformation> posToSymbol = new HashMap<CellSpaceInformation, DataSymbolInformation>();
		for (DataSymbolInformation dataSymbol : dataSymbols)
			posToSymbol.put(dataSymbol.getPostition(), dataSymbol);	// Limited to one symbol per position at the moment.
		for (Relation rel : manager.getRelationsFor(null,  null, Relation.RelationType.FUNCTIONALRELATION)) {
			for (CellTuple cellEntry : rel.getCellRelations()) {
				String assertion = "(assert (= (" + uriToIdentifier(rel.getUri()) + " ";
				for (int i = 0; i < cellEntry.getSize() - 1; i++) {
					String basicType = manager.getOntologyInterface().getDataTypeObject(posToSymbol.get(cellEntry.getTuple().get(i)).getOntologyType()).getBasicType().name();
					assertion += "(value-" + basicType + " Sym-" + posToSymbol.get(cellEntry.getTuple().get(i)).getSymbolID() + ") ";
				}
				int lastIndex = cellEntry.getSize() - 1;
				String basicType = manager.getOntologyInterface().getDataTypeObject(posToSymbol.get(cellEntry.getTuple().get(lastIndex)).getOntologyType()).getBasicType().name();
				assertion += ") " + "(value-" + basicType + " Sym-" + posToSymbol.get(cellEntry.getTuple().get(lastIndex)).getSymbolID() + ") ) ) ";
				specifications.add(assertion);
			}
		}
		return specifications;
	}
	
	public static String getAxiom(Manager manager, AxiomObject axiom, List<DataSymbolInformation> dataSymbols) {	
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
			axiomSpec += ")\n";
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
		axiomSpec += "(=>\n  (and\n";
		for (String v : varType.keySet())
			axiomSpec += "     (is-" + uriToIdentifier(varType.get(v)) + " " + v + ")\n";
		
		if (!axiom.getVarConditions().isEmpty())
			axiomSpec += ml2Z3(axiom.getVarConditions(), mathML2Z3XLSTFunctions) + "\n";
		
		// Replace identifiers with Z3 valid name
		String mlDef = axiom.getMLConstrain();
		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntologyInterface().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlDef = mlDef.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}

		for (AxiomVariableObject var : axiom.getVariables()) {
			String varBaisType = manager.getOntologyInterface().getDataTypeObject(var.getType()).getBasicType().name();
			mlDef = mlDef.replaceAll(manager.getOntologyInterface().getBuilderML().getIdentifier(var.getName()),  " (value-" + varBaisType + " " + var.getName() + ") ");
		}
					
		axiomSpec += "  )\n  " + ml2Z3(mlDef, mathML2Z3XLSTFunctions) + ")\n";
		
		//axiomSpec += "  )\n  " + mathML2Z3(axiom.getMLConstrain(), mathML2Z3XLSTFunctions, identifierToSymbol) + ")\n";
		
		if (!existQuantVars.isEmpty())
			axiomSpec += ")";
		
		if (!allQuantVars.isEmpty())
			axiomSpec += ")";

		return axiomSpec + ")";
	}
	
	public static String getCPSimilarBlockSpec(Manager manager, CPSimilarBlockData cpBlock, List<DataSymbolInformation> dataSymbols) {
		
		FunctionObject func = manager.getOntologyInterface().getFunctionObject(cpBlock.getRelation().getUri());
		Map<Integer, String> constantArguments = cpBlock.getConstantArguments();
		Map<String, DataSymbolInformation> identifierToSymbol = new HashMap<String, DataSymbolInformation>();
		for (DataSymbolInformation d : dataSymbols)
			identifierToSymbol.put(d.getContent(), d);		// TODO: content should not be an unique identifier for a dataSymbol
		
		String funcSpec = "(assert (not (forall (";
		for (int i = 0; i < func.getArgumentTypes().size(); i++)
			if (!constantArguments.containsKey(new Integer(i)))
				funcSpec += "(x" + i + " Object)";
		
		funcSpec += ")\n (=> (and \n";
		for (int i = 0; i < func.getArgumentTypes().size(); i++)
			if (!constantArguments.containsKey(new Integer(i)))
				funcSpec += " (is-" + uriToIdentifier(func.getArgumentTypes().get(i)) + " x" + i + ") " ;
		
		funcSpec += ")\n";
		
		// Replace identifiers with Z3 valid name
		String mlRep = cpBlock.getAntiunification();
		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntologyInterface().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlRep = mlRep.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}
		
		String z3DefRep = ml2Z3(mlRep, mathML2Z3XLSTFunctions) + "))))";
		for (int i = 0; i < func.getArgumentTypes().size(); i++) {
			String varBaisType = manager.getOntologyInterface().getDataTypeObject(func.getArgumentTypes().get(i)).getBasicType().name();
			if (!constantArguments.keySet().contains(i))
				z3DefRep = z3DefRep.replaceAll("(\\n|\\s)x" + i + " ",  " (value-" + varBaisType + " x" + i + ") ");
			else {
				
				z3DefRep = z3DefRep.replaceAll("(\\n|\\s)x" + i + " ", " (value-" + varBaisType + " Sym-" + identifierToSymbol.get(constantArguments.get(i)).getSymbolID() + ") ");
			}
		}
		
		funcSpec += z3DefRep;
		
		return funcSpec;
	}
	
	private static String getFunctionDeclaration(FunctionObject function, Manager manager) {
		String funcDef = "(declare-fun " + uriToIdentifier(function.getUri()) + " (";
		for (String argType : function.getArgumentTypes()) {
			funcDef = funcDef +  manager.getOntologyInterface().getDataTypeObject(argType).getBasicType().name() + " ";
		}
		return funcDef + ") " + manager.getOntologyInterface().getDataTypeObject(function.getResultType()).getBasicType().name() + ")";
	}
	
	//private static String getFunctionDefinition(FunctionObject function, Manager manager, Map<String, String> viToZ3String) {
	private static String getFunctionDefinition(FunctionObject function, Manager manager, List<DataSymbolInformation> dataSymbols) {
		String funcDef = "(define-fun " + uriToIdentifier(function.getUri()) + " (";
		for (int i = 0; i < function.getArgumentTypes().size(); i++) 
			funcDef += "(x" + i + " " + manager.getOntologyInterface().getDataTypeObject(function.getArgumentTypes().get(i)).getBasicType().name() + ")";
		funcDef += ") " +  manager.getOntologyInterface().getDataTypeObject(function.getResultType()).getBasicType().name() + "\n";
		
		// Replace identifiers with Z3 valid name
		String mlDef = function.getMLDefinition();
		

		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntologyInterface().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlDef = mlDef.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}
		
		//for (String vi : viToZ3String.keySet())
		//	mlDef = mlDef.replaceAll(vi, viToZ3String.get(vi));
		
		funcDef = funcDef + ml2Z3(mlDef, mathML2Z3XLSTFunctions);
		funcDef += "\n)";
		return funcDef;
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
