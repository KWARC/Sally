package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

public class VerificationSpecificationGeneratorTest {
	Manager manager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
	}

	@Test
	public void testGetDataTypeSpecification() {
		// Datatypes
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());
			
		}
		List<DataSymbolInformation> dataSym = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		List<String> dtSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym);
		for (DataSymbolInformation symbol : dataSym)
			dtSpec.add(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol));
		
		assertTrue(dtSpec.size() == 39);
		/*System.out.println("Data specification. Size: " + dtSpec.size());
		for (String s : dtSpec)
			System.out.println(s);*/
	}

	@Test
	public void testCreateFunctionDeclarations() {
		List<String> declarations = VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllDomainFunctionObjects(), manager);
		assertTrue(declarations.size() == 2);
		assertEquals("(declare-fun revenues~RevenuesPerYear (String ) Real)", declarations.get(0));
		assertEquals("(declare-fun expenses~ExpensesPerYear (String String ) Real)", declarations.get(1));
		
		/*System.out.println("Declarations");
		for (String s : declarations)
			System.out.println(s);*/
	}

	@Test
	public void testCreateFunctionDefinitions() {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		//DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataTypes);

		List<String> definitions = VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllDomainFunctionObjects(), manager, dataTypes);
		assertTrue(definitions.size() == 1);
		assertEquals(
				"(define-funprofits~ProfitPerYear((x0String))Real"
				+ "("
				+ "spsht-arith~minus"
				+ "("
				+ "revenues~RevenuesPerYear"
				+ "x0"
				+ ")"
				+ "("
				+ "expenses~ExpensesPerYear"
				+ "x0"
				+ "(value-StringSym-7)"
				+ ")"
				+ "))", 
				definitions.get(0).replaceAll(" ", "").replaceAll("\r", "").replaceAll("\n", ""));
		
		/*System.out.println("Function definitions:");
		for (String def : definitions)
			System.out.println(def);*/
	}
	
	@Test
	public void testCreateFunctionSymbolAssertions() {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		List<String> spec = VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataTypes);
		
		assertTrue(spec.size() == 20);
		assertEquals("(assert (= (revenues~RevenuesPerYear (value-String Sym-1) ) (value-Real Sym-16) ) ) ", spec.get(0));
		
		/*System.out.println("Assertions:");
		for (String s : spec)
			System.out.println(s);*/
	}
	
	@Test
	public void testCreateAxiom() {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		//DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataTypes);
		
		String axiomSpec = VerificationSpecificationGenerator.getAxiom(manager, manager.getOntologyInterface().getAxioms().get(0), dataTypes);
		//System.out.println("Axiom Specification:\n" + axiomSpec);
		assertEquals(
				  "(assert (forall ((y Object))\n"
				+ "(=>\n"
				+ "(and\n"
				+ "(is-timeinterval~yearAD y)\n"
				+ ")\n"
				+ "(spsht-arith~equal (expenses~ExpensesPerYear  (value-String y)  (value-String Sym-7) )(spsht-arith~plus (expenses~ExpensesPerYear  (value-String y)  (value-String Sym-6) )(expenses~ExpensesPerYear  (value-String y)  (value-String Sym-5) ))))\n"
				+ "))", axiomSpec.replaceAll("\\n\\s+", "\n") );
	}
	
	@Test
	public void testGetCPSimilarBlockSpec() {
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML());
		//Relation firstRel = (Relation) cpBlocks.keySet().toArray()[0];
		
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		
		CPSimilarBlockData profitBlock = null;
		for (CPSimilarBlockData b : cpBlocks)
			if (b.getRelation().equals(winData.getRelationProfit()))
				profitBlock = b;
		
		String spec = VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, profitBlock, dataTypes);
		//System.out.println("CP Similar specification:\n" + spec);
		assertEquals(
				  "(assert (not (forall ((x0 Object))\n"
				+ "(=> (and\n"
				+ "(is-timeinterval~yearAD x0) )\n"
				+ "(\n"
				+ "spsht-arith~equal \n"
				+ "(\n"
				+ "profits~ProfitPerYear  (value-String x0) \n"
				+ ")\n"
				+ "(\n"
				+ "spsht-arith~minus\n"
				+ "(\n"
				+ "revenues~RevenuesPerYear\n"
				+ "(value-String x0)\n"
				+ ")\n"
				+ "(\n"
				+ "expenses~ExpensesPerYear\n"
				+ "(value-String x0)\n"
				+ "(value-String Sym-7)\n"
				+ ")\n"
				+ ")\n"
				+ ")\n"
				+ "))))"
				, spec.replaceAll("\\s*\\n\\s+", "\n"));
	}
	
	@Test
	public void testGetFormulaSpec() {
		Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
		List<DataSymbolInformation> dataSymbols = VerificationDataExtractor.extractDataTypes(manager.getBlockTypes(manager.getAllTopLevelBlocks()), spreadsheet);
		
		String specification = VerificationSpecificationGenerator.getFormulaSpec(manager, winData.getRelationProfit(), "C2-C5", new CellSpaceInformation("Table1",5,2), interpretation, dataSymbols);
		assertEquals(
				  "(assert (spsht-arith~equal \n"
				+ "(profits~ProfitPerYear (value-String Sym-2) )\n"
				+ "(\n"
				+ "spsht-arith~minus\n"
				+ "(\n"
				+ "revenues~RevenuesPerYear\n"
				+ "(value-String Sym-2)\n"
				+ ")\n"
				+ "(\n"
				+ "expenses~ExpensesPerYear\n"
				+ "(value-String Sym-2)\n"
				+ "(value-String Sym-7)\n"
				+ ")\n"
				+ ")\n"
				+ "))"
				, specification.replaceAll("\\s*\\n\\s+", "\n"));
	}

	@Test
	public void testCreateCompeteSpecification() {
		try{
			PrintWriter pWriter = new PrintWriter(new FileWriter("specification.z3"));
	        for (String line : VerificationSpecificationGenerator.createCompeteSpecification(manager, spreadsheet))
	        	pWriter.println(line);
	        pWriter.flush();
	        pWriter.close();
	    }catch(IOException ioe){
	        ioe.printStackTrace();
	    } 
	}

}
