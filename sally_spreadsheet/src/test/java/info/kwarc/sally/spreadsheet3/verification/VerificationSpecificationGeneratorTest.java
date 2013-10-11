package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;

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
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		List<String> dtSpec = VerificationSpecificationGenerator.getDataTypeSpecification(dataTypes).getSpecification();
		assertTrue(dtSpec.size() == 32);
		assertEquals("(declare-datatypes () ((Object Sym-26 Sym-24 Sym-25 Sym-22 Sym-23 Sym-20 Sym-21 Sym-3 Sym-2 Sym-5 Sym-4 Sym-1 Sym-0 Sym-17 Sym-18 Sym-19 Sym-13 Sym-14 Sym-15 Sym-16 Sym-10 Sym-11 Sym-12 Sym-6 Sym-7 Sym-8 Sym-9 )))",
				dtSpec.get(0));
		assertEquals("(assert (= Sym-26 Profit ) )", dtSpec.get(1));
	}

	@Test
	public void testCreateFunctionDeclarations() {
		List<String> declarations = VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllFunctionObjects());
		assertTrue(declarations.size() == 2);
		assertEquals("(declare-fun winograd~ExpensesPerYear (Object Object ) Real)", declarations.get(0));
		assertEquals("(declare-fun winograd~RevenuePerYear (Object ) Real)", declarations.get(1));
	}

	@Test
	public void testCreateFunctionDefinitions() {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : manager.getAllTopLevelBlocks()) {
			Relation blockRelation = manager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		Map<String, List<String>> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(dataTypes);
		/*System.out.println("Function definitions:");
		for (String def : VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllFunctionObjects(), dataTypesSpec.getIdentifierToSymbol()))
			System.out.println(def);*/
		List<String> definitions = VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllFunctionObjects(), dataTypesSpec.getIdentifierToSymbol());
		assertEquals("(define-fun spsht-arith~minus ((x0 Real)(x1 Real)) Real\n(- x0 x1 )\n)", definitions.get(0));
	}
	
	@Test
	public void testCreateAxiom() {
		String axiom = manager.getOntologyInterface().getAxioms().get(0);
		System.out.println("Axiom:");
		System.out.println(VerificationSpecificationGenerator.getAxiom(axiom));
	}

	@Ignore
	public void testCreateCompeteSpecification() {
		fail("Not yet implemented");
	}

}
