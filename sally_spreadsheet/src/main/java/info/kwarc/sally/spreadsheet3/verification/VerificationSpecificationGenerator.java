package info.kwarc.sally.spreadsheet3.verification;


import info.kwarc.sally.spreadsheet3.Manager;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.logic.RelationInterpreter;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.AxiomVariableObject;
import info.kwarc.sally.spreadsheet3.ontology.DataTypeObject;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.OntologyException;

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

/**
 * This class provides methods to generate Z3 verification specifications. 
 * @author cliguda
 *
 */
public class VerificationSpecificationGenerator {
	
	//final static String mathML2Z3XLSTTypes = "src/main/resources/MathML2Z3Types.xsl";
	final static String mathML2Z3XLST = "src/main/resources/info/kwarc/sally/spreadsheet3/verification/MathML2Z3.xsl";
	final static String mathML2Z3XLSTAxioms = "src/main/resources/info/kwarc/sally/spreadsheet3/verification/MathML2Z3Axioms.xsl";
	final static Logger logger = LoggerFactory.getLogger(VerificationSpecificationGenerator.class);
	static psf.ParserInterface parser = new psf.ParserInterface();
	
	/**
	 * Create a complete Z3 specification for a given spreadsheet. 
	 * Mostly used for testing purposes.
	 * @param manager
	 * @param spreadsheet
	 * @return
	 * @throws ModelException 
	 * @throws OntologyException 
	 */
	public static List<String> createCompeteSpecification(Manager manager) throws ModelException, OntologyException {
		List<String> specification = new ArrayList<String>();
		
		// Datatypes
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getModel().getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getModel().getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());
		}
		List<DataSymbolInformation> dataSym = VerificationDataExtractor.extractDataTypes(blocks, manager.getSpreadsheet());
		
		// Specification of symbols, axioms and functions
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntology().getAllBasicFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntology().getAllBasicFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntology().getAllDomainFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntology().getAllDomainFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSym));
		
		for (AxiomObject axiom : manager.getOntology().getAxioms())
			specification.add(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym));
		
		specification.add("(check-sat)\n");
		
		// Checking cp-similar blocks
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(manager);
		
		for (CPSimilarBlockData cpBlock : cpBlocks) {
			specification.add("(push)\n");
			specification.add( VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym));
			specification.add("(check-sat)\n");
			specification.add("(pop)\n");
		}
		
		return specification;
	
	}
	
	/**
	 * The specification uses only one datatype "Object" that contains all symbols. 
	 * Other datatypes like "Years" or "Costtype" are indirectly specified by functions that determine the associated datatype.
	 * @see getDataTypeSpecification
	 * @param dataSymbols
	 * @return
	 */
	public static String getObjectSymbolSpecification(List<DataSymbolInformation> dataSymbols) {
		// Generating symbols
		String objectDefinition = "(declare-datatypes () ((Object ";
				
		for (DataSymbolInformation dataSymbol :  dataSymbols) 
			objectDefinition += "Sym-" + dataSymbol.getSymbolID() + " ";
			
		return (objectDefinition + ")))");
		
		
	}
	
	/**
	 * Generates functions to determine the associated datatypes of symbols and declares functions to assign symbols to functions.
	 * @param manager
	 * @param dataSymbols
	 * @return
	 */
	public static List<String> getDataTypeSpecification(Manager manager, List<DataSymbolInformation> dataSymbols) {
		List<String> specification = new ArrayList<String>();
		//Map<String, String> viToZ3String = new HashMap<String,String>();
		
		// Generating datatype String
		boolean stringDataTypes = false;
		for (DataSymbolInformation symbol : dataSymbols) {
			if (manager.getOntology().getDataTypeObject(symbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String) {
				//viToZ3String.put(symbol.getContent(), toZ3Value(ml2Z3(symbol.getContent(), mathML2Z3XLST)));
				//symbol.setZ3String(toZ3Value(ml2Z3(symbol.getContent(), mathML2Z3XLST)));
				stringDataTypes = true;
			}
		}
		/*if (!viToZ3String.values().isEmpty()) {
			String stringDefinition = "(declare-datatypes () ((String ";
			for (String s : viToZ3String.values())
				stringDefinition += s + " ";
			stringDefinition += ")))";
			specification.add(stringDefinition);
		}*/
		if (stringDataTypes) {
			String stringDefinition = "(declare-datatypes () ((String ";
			for (DataSymbolInformation dataSymbol : dataSymbols)
				if ((manager.getOntology().getDataTypeObject(dataSymbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String) && !toZ3Value(dataSymbol.getContent()).isEmpty())
					stringDefinition += toZ3Value(dataSymbol.getContent()) + " ";
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
		/*
		for (DataSymbolInformation symbol : dataSymbols) {
			String value =  ml2Z3(symbol.getContent(),mathML2Z3XLST);
			if (manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String)
				value = toZ3Value(value);
			if (!value.isEmpty())
				specification.add("(assert (= (value-" + manager.getOntologyInterface().getDataTypeObject(symbol.getOntologyType()).getBasicType().name() + " Sym-" + symbol.getSymbolID() + ") " + value + "))");
		}*/
		//return new DataTypeSpec(specification, viToZ3String);
		return specification;
	}
	
	/**
	 * Creates a specification to assign values (value interpretations) to symbols.
	 * @param manager
	 * @param symbol
	 * @return
	 */
	public static String createSymbolValueAssertion(Manager manager, DataSymbolInformation symbol) {
		String value = "";
		
		if (manager.getOntology().getDataTypeObject(symbol.getOntologyType()).getBasicType() == DataTypeObject.BasicType.String)
			value = toZ3Value(symbol.getContent());
		else
			value = ml2Z3(symbol.getContent(), mathML2Z3XLST);
		
		if (!value.isEmpty())
			return "(assert (= (value-" + manager.getOntology().getDataTypeObject(symbol.getOntologyType()).getBasicType().name() + " Sym-" + symbol.getSymbolID() + ") " + value + "))";
		else
			return "";
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
	
	/**
	 * Creates to connection between symbols and functions, e.g. that a symbol represents the cell that contains the value for profit (1984).
	 * @param manager
	 * @param dataSymbols
	 * @return
	 * @throws ModelException
	 */
	public static List<String> createFunctionSymbolAssertions(Manager manager, List<DataSymbolInformation> dataSymbols) throws ModelException {
		List<String> specifications = new ArrayList<String>();
		
		Map<CellSpaceInformation, DataSymbolInformation> posToSymbol = new HashMap<CellSpaceInformation, DataSymbolInformation>();
		for (DataSymbolInformation dataSymbol : dataSymbols)
			posToSymbol.put(dataSymbol.getPostition(), dataSymbol);	// Limited to one symbol per position at the moment.
		for (Relation rel : manager.getModel().getRelationsFor(null,  null, Relation.RelationType.FUNCTIONALRELATION)) {
			for (CellTuple cellEntry : rel.getCellRelations()) {
				
				String assertion = "(assert (= " + position2Z3Function(rel,  cellEntry, manager, dataSymbols);
				int lastIndex = cellEntry.getSize() - 1;
				String basicType = manager.getOntology().getDataTypeObject(posToSymbol.get(cellEntry.getTuple().get(lastIndex)).getOntologyType()).getBasicType().name();
				assertion += " (value-" + basicType + " Sym-" + posToSymbol.get(cellEntry.getTuple().get(lastIndex)).getSymbolID() + ") ) ) ";
				specifications.add(assertion);
			}
		}
		return specifications;
	}
	
	/** 
	 * Creates a specification for an axiom.
	 * @param manager
	 * @param axiom
	 * @param dataSymbols
	 * @return
	 */
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
				/*if (isStandardType(var.getType()))
					axiomSpec += "(" + var.getName() + " " + uriToIdentifier(var.getType()) + ")";
				else {
					axiomSpec += "(" + var.getName() + " Object)";
					varType.put(var.getName(), var.getType());
				}*/
				axiomSpec += "(" + var.getName() + " Object)";
				varType.put(var.getName(), var.getType());
			}
			axiomSpec += ")\n";
		}
		if (!existQuantVars.isEmpty()) {
			axiomSpec += "(exists (";
			for (AxiomVariableObject var : existQuantVars) {
				/*if (isStandardType(var.getType()))
					axiomSpec += "(" + var.getName() + " " + uriToIdentifier(var.getType()) + ")";
				else {
					axiomSpec += "(" + var.getName() + " Object)";
					varType.put(var.getName(), var.getType());
				}*/
				axiomSpec += "(" + var.getName() + " Object)";
				varType.put(var.getName(), var.getType());
			}
			axiomSpec += "\n";
		}
		axiomSpec += "(=>\n  (and\n";
		for (String v : varType.keySet())
			axiomSpec += "     (is-" + uriToIdentifier(varType.get(v)) + " " + v + ")\n";
		
		if (!axiom.getVarConditions().isEmpty())
			axiomSpec += ml2Z3(axiom.getVarConditions(), mathML2Z3XLST) + "\n";
		
		// Replace identifiers with Z3 valid name
		String mlDef = axiom.getMLConstrain();
		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntology().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlDef = mlDef.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}

		for (AxiomVariableObject var : axiom.getVariables()) {
						
			String varBasicType = manager.getOntology().getDataTypeObject(var.getType()).getBasicType().name();
			mlDef = mlDef.replaceAll(manager.getOntology().getBuilderML().getIdentifier(var.getName()),  " (value-" + varBasicType + " " + var.getName() + ") ");
		}
					
		axiomSpec += "  )\n  " + ml2Z3(mlDef, mathML2Z3XLST) + ")\n";
		
		//axiomSpec += "  )\n  " + mathML2Z3(axiom.getMLConstrain(), mathML2Z3XLSTFunctions, identifierToSymbol) + ")\n";
		
		if (!existQuantVars.isEmpty())
			axiomSpec += ")";
		
		if (!allQuantVars.isEmpty())
			axiomSpec += ")";

		return axiomSpec + ")";
	}
	
	/**
	 * Creates a specification for a cp-similar block.
	 * @param manager
	 * @param cpBlock
	 * @param dataSymbols
	 * @return
	 */
	public static String getCPSimilarBlockSpec(Manager manager, CPSimilarBlockData cpBlock, List<DataSymbolInformation> dataSymbols) {
		
		FunctionObject func = manager.getOntology().getFunctionObject(cpBlock.getRelation().getUri());
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
			String basicType = manager.getOntology().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlRep = mlRep.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}
		
		String z3DefRep = ml2Z3(mlRep, mathML2Z3XLST) + "))))";
		for (int i = 0; i < func.getArgumentTypes().size(); i++) {
			String varBaisType = manager.getOntology().getDataTypeObject(func.getArgumentTypes().get(i)).getBasicType().name();
			if (!constantArguments.keySet().contains(i))
				z3DefRep = z3DefRep.replaceAll("(\\n|\\s)x" + i + " ",  " (value-" + varBaisType + " x" + i + ") ");
			else {
				
				z3DefRep = z3DefRep.replaceAll("(\\n|\\s)x" + i + " ", " (value-" + varBaisType + " Sym-" + identifierToSymbol.get(constantArguments.get(i)).getSymbolID() + ") ");
			}
		}
		
		funcSpec += z3DefRep;
		
		return funcSpec;
	}
	
	/**
	 * Creates a specification for a cell formula.
	 * Thereby the position of a cell is mapped to a specification of the corresponding ontology function (e.g. profit(1984) ) which should be the same as the transformed cell formula.
	 * @param manager
	 * @param relation
	 * @param formula
	 * @param position
	 * @param interpretation
	 * @param dataSymbols
	 * @return
	 * @throws ModelException
	 */
	public static String getFormulaSpec(Manager manager, Relation relation, String formula, CellSpaceInformation position, Map<CellSpaceInformation, String> interpretation, List<DataSymbolInformation> dataSymbols) throws ModelException {
		// Function begin
		String specification = "(assert (not (spsht-arith~equal \n" +  position2Z3Function(relation,  relation.getCellRelationFor(position).get(0), manager, dataSymbols);
		
		// Formula parsing
		psf.SemanticMapping mapping = new psf.SemanticMapping();
		for (CellSpaceInformation pos : interpretation.keySet()) 
			mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
		psf.ParserParameter p = new psf.ParserParameter(formula, position.getWorksheet(), false, true, false, true, mapping.getMapping());
		String mlRep = parser.parseFormula(p).getMathML();
		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntology().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlRep = mlRep.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}
		
		// Z3 transformation and formula ending
		specification += ml2Z3(mlRep, mathML2Z3XLST) + ")))";
		return specification;
	}
	
	/**
	 * Declares a function from the ontology.
	 * @param function
	 * @param manager
	 * @return
	 */
	private static String getFunctionDeclaration(FunctionObject function, Manager manager) {
		String funcDef = "(declare-fun " + uriToIdentifier(function.getUri()) + " (";
		for (String argType : function.getArgumentTypes()) {
			funcDef = funcDef +  manager.getOntology().getDataTypeObject(argType).getBasicType().name() + " ";
		}
		return funcDef + ") " + manager.getOntology().getDataTypeObject(function.getResultType()).getBasicType().name() + ")";
	}
	
	/**
	 * Defines a function from the ontology. 
	 * @param function
	 * @param manager
	 * @param dataSymbols
	 * @return
	 */
	private static String getFunctionDefinition(FunctionObject function, Manager manager, List<DataSymbolInformation> dataSymbols) {
		String funcDef = "(define-fun " + uriToIdentifier(function.getUri()) + " (";
		for (int i = 0; i < function.getArgumentTypes().size(); i++) 
			funcDef += "(x" + i + " " + manager.getOntology().getDataTypeObject(function.getArgumentTypes().get(i)).getBasicType().name() + ")";
		funcDef += ") " +  manager.getOntology().getDataTypeObject(function.getResultType()).getBasicType().name() + "\n";
		
		// Replace identifiers with Z3 valid name
		String mlDef = function.getMLDefinition();
		

		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntology().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			mlDef = mlDef.replaceAll(di.getContent(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") ");
		}
		
		//for (String vi : viToZ3String.keySet())
		//	mlDef = mlDef.replaceAll(vi, viToZ3String.get(vi));
		
		funcDef = funcDef + ml2Z3(mlDef, mathML2Z3XLST);
		funcDef += "\n)";
		return funcDef;
	}
	
	/**
	 * Transforms a MathML or OpenMath expression to Z3 syntax by using XLST transformations.
	 * @param expression
	 * @param template
	 * @return
	 */
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
	
	/**
	 * Transforms an URI that points to an Omdoc resource to a Z3 identifier of the format contentDictionary~SymbolName
	 * @param uri
	 * @return
	 */
	private static String uriToIdentifier(String uri) {
		if (Util.isOMDocUri(uri)) {
			/*if (isStandardType(uri))
				return Util.getSymbolFromURI(uri);
			else
				return Util.getCDFromURI(uri) + "~" + Util.getSymbolFromURI(uri);*/
			return Util.getCDFromURI(uri) + "~" + Util.getSymbolFromURI(uri);
		} else
			return "";
	}
	
	/**
	 * 
	 * @param uri
	 * @return
	 *
	private static Boolean isStandardType(String uri) {
		String[] mathMLDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
		boolean isMathMLDT = false;
		for (String dt : mathMLDataTypes)
			if (dt.equals(uri) )
				isMathMLDT = true;
		return isMathMLDT;
	}*/
	
	/**
	 * Transforms a string to Z3 and replaces whitespaces by "-".
	 * @param s
	 * @return
	 */
	private static String toZ3Value(String s) {
		return ml2Z3(s, mathML2Z3XLST).trim().replaceAll(" ", "-");
	}
	
	/**
	 * Creates a Z3 function call for a given cell.
	 * @param relation
	 * @param cells
	 * @param manager
	 * @param dataSymbols
	 * @return
	 * @throws ModelException
	 */
	private static String position2Z3Function(Relation relation, CellTuple cells, Manager manager, List<DataSymbolInformation> dataSymbols) throws ModelException {
		Map<CellSpaceInformation, String> posToSymbolName = new HashMap<CellSpaceInformation, String>();
		for (DataSymbolInformation symbol : dataSymbols) {
			posToSymbolName.put(symbol.getPostition(), "Sym-" + symbol.getSymbolID());
			// System.out.println("Map: " + symbol.getPostition() + " -> " + symbol.getSymbolID());
		}
		String relationInterpretation = ml2Z3(RelationInterpreter.interprete(relation, cells, manager.getSpreadsheet(), manager.getOntology(), posToSymbolName ), mathML2Z3XLST);
		//System.out.println("relation Interpretation: " + relationInterpretation );
		for (DataSymbolInformation di : dataSymbols) {
			String basicType = manager.getOntology().getDataTypeObject(di.getOntologyType()).getBasicType().name();
			relationInterpretation = relationInterpretation.replaceAll("Sym-" + di.getSymbolID(), " (value-" + basicType + " Sym-" + di.getSymbolID() + ") "); 	
		}
		
		return relationInterpretation;
	}

}
