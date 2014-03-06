package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;
import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

public class VerificationSpecificationGeneratorTest {
	Manager manager;
	FormalSpreadsheet spreadsheet;

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
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
		List<String> dtSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym).getSpecification();
		
		assertTrue(dtSpec.size() == 40);
		/*System.out.println("Data specification. Size: " + dtSpec.size());
		for (String s : dtSpec)
			System.out.println(s);*/
	}

	@Test
	public void testCreateFunctionDeclarations() {
		List<String> declarations = VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllFunctionObjects(), manager);
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
		DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataTypes);

		List<String> definitions = VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllFunctionObjects(), manager, dataTypesSpec.getViToZ3StringMap());
		assertTrue(definitions.size() == 6);
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
				+ "Total-Costs"
				+ ")"
				+ "))", 
				definitions.get(0).replaceAll(" ", "").replaceAll("\r", "").replaceAll("\n", ""));
		
		/*System.out.println("Function definitions:");
		for (String def : definitions)
			System.out.println(def);*/
	}
	
	/*
	@Test
	public void testCreateAxiom() {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(dataTypes);
		
		String axiomSpec = VerificationSpecificationGenerator.getAxiom(manager.getOntologyInterface().getAxioms().get(0), dataTypesSpec.getIdentifierToSymbol());
		System.out.println("Axiom Specification:\n" + axiomSpec);
	}*/

	@Ignore
	public void testCreateCompeteSpecification() {
		fail("Not yet implemented");
	}

}
