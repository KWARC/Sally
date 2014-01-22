package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Manager;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;
import info.kwarc.sally.spreadsheet3.ontology.OntologyException;

import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Before;
import org.junit.Test;

public class VerificationSpecificationGeneratorTest {
	Manager manager;
	ModelManager modelManager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	IOntologyProvider ontology;

	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		manager = winData.getManager();
		modelManager = winData.getModelManager();
		spreadsheet = winData.getSpreadsheet();
		ontology = winData.getManager().getOntology();
	}

	@Test
	public void testGetDataTypeSpecification() throws ModelException {
		// Datatypes
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : modelManager.getAllTopLevelBlocks()) {
			Relation blockRelation = modelManager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
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
		List<String> declarations = VerificationSpecificationGenerator.createFunctionDeclarations(ontology.getAllDomainFunctionObjects(), manager);
		assertTrue(declarations.size() == 2);
		assertEquals("(declare-fun sax-revenues~sax-revenuesperti (String ) Real)", declarations.get(0));
		assertEquals("(declare-fun sax-costs~sax-costsperti (String String ) Real)", declarations.get(1));
		
		/*System.out.println("Declarations");
		for (String s : declarations)
			System.out.println(s);*/
	}

	@Test
	public void testCreateFunctionDefinitions() throws ModelException {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : modelManager.getAllTopLevelBlocks()) {
			Relation blockRelation = modelManager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		//DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataTypes);

		List<String> definitions = VerificationSpecificationGenerator.createFunctionDefinitions(ontology.getAllDomainFunctionObjects(), manager, dataTypes);
		assertTrue(definitions.size() == 1);
		assertEquals(
				"(define-funsax-profit~sax-profitperti((x0String))Real(spsht-arith~minus(sax-revenues~sax-revenuespertix0)(sax-costs~sax-costspertix0(value-StringSym-7))))", 
				definitions.get(0).replaceAll(" ", "").replaceAll("\r", "").replaceAll("\n", ""));
		
		/*System.out.println("Function definitions:");
		for (String def : definitions)
			System.out.println(def);*/
	}
	
	@Test
	public void testCreateFunctionSymbolAssertions() throws ModelException {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : modelManager.getAllTopLevelBlocks()) {
			Relation blockRelation = modelManager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		List<String> spec = VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataTypes);
		
		assertTrue(spec.size() == 20);
		assertEquals("(assert (= (\nsax-revenues~sax-revenuesperti \n (value-String Sym-1)  \n) (value-Real Sym-16) ) ) ", spec.get(0));
		
		/*System.out.println("Assertions:");
		for (String s : spec)
			System.out.println(s);*/
	}
	
	@Test
	public void testCreateAxiom() throws ModelException, OntologyException {
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : modelManager.getAllTopLevelBlocks()) {
			Relation blockRelation = modelManager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
			blocks.put(b, blockRelation.getUri());	
		}
		List<DataSymbolInformation> dataTypes = VerificationDataExtractor.extractDataTypes(blocks, spreadsheet);
		//DataTypeSpec dataTypesSpec = VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataTypes);
		
		String axiomSpec = VerificationSpecificationGenerator.getAxiom(manager, ontology.getAxioms().get(0), dataTypes);
		//System.out.println("Axiom Specification:\n" + axiomSpec);
		assertEquals(
				  "(assert (forall ((y Object))\n"
				+ "(=>\n"
				+ "(and\n"
				+ "(is-timeinterval~yearAD y)\n"
				+ ")\n"
				+ "(spsht-arith~equal (sax-costs~sax-costsperti  (value-String y)  (value-String Sym-7) )(spsht-arith~plus (sax-costs~sax-costsperti  (value-String y)  (value-String Sym-6) )(sax-costs~sax-costsperti  (value-String y)  (value-String Sym-5) ))))\n"
				+ "))", axiomSpec.replaceAll("\\n\\s+", "\n") );
	}
	
	@Test
	public void testGetCPSimilarBlockSpec() throws ModelException {
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(manager);
		//Relation firstRel = (Relation) cpBlocks.keySet().toArray()[0];
		
		Map<Block, String> blocks = new HashMap<Block, String>();
		for (Block b : modelManager.getAllTopLevelBlocks()) {
			Relation blockRelation = modelManager.getRelationsFor(null, b, Relation.RelationType.TYPERELATION).get(0);
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
				+ "sax-profit~sax-profitperti  (value-String x0) \n"
				+ ")\n"
				+ "(\n"
				+ "spsht-arith~minus\n"
				+ "(\n"
				+ "sax-revenues~sax-revenuesperti\n"
				+ "(value-String x0)\n"
				+ ")\n"
				+ "(\n"
				+ "sax-costs~sax-costsperti\n"
				+ "(value-String x0)\n"
				+ "(value-String Sym-7)\n"
				+ ")\n"
				+ ")\n"
				+ ")\n"
				+ "))))"
				, spec.replaceAll("\\s*\\n\\s+", "\n"));
	}
	
	@Test
	public void testGetFormulaSpec() throws ModelException {
		Map<CellSpaceInformation, String> interpretation = modelManager.getCompleteSemanticMapping(spreadsheet, ontology);
		List<DataSymbolInformation> dataSymbols = VerificationDataExtractor.extractDataTypes(modelManager.getBlockTypes(modelManager.getAllTopLevelBlocks()), spreadsheet);
		
		String specification = VerificationSpecificationGenerator.getFormulaSpec(manager, winData.getRelationProfit(), "C2-C5", new CellSpaceInformation("Table1",5,2), interpretation, dataSymbols);
		assertEquals(
				  "(assert (not (spsht-arith~equal \n"
				+ "(\n"
				+ "sax-profit~sax-profitperti\n"
				+ "(value-String Sym-2)  \n"
				+ ")\n"
				+ "(\n"
				+ "spsht-arith~minus\n"
				+ "(\n"
				+ "sax-revenues~sax-revenuesperti\n"
				+ "(value-String Sym-2)\n"
				+ ")\n"
				+ "(\n"
				+ "sax-costs~sax-costsperti\n"
				+ "(value-String Sym-2)\n"
				+ "(value-String Sym-7)\n"
				+ ")\n"
				+ ")\n"
				+ ")))"
				, specification.replaceAll("\\s*\\n\\s+", "\n"));
		
		winData.createSecondeTCRelation();
		specification = VerificationSpecificationGenerator.getFormulaSpec(manager, winData.getRelationTotalCosts2(), "C3+C4", new CellSpaceInformation("Table1",4,2), interpretation, dataSymbols);
		assertEquals(
				"(assert (not (spsht-arith~equal \n" + 
				"(\n" +
				"sax-costs~sax-costsperti\n" +
				"(value-String Sym-2)  \n" + 
				"Total Costs \n" + 
				")\n" +
				"(\n" +
				"spsht-arith~plus\n" + 
				"(\n" +
				"sax-costs~sax-costsperti\n" +  
				"(value-String Sym-2)\n" + 
				"(value-String Sym-5)\n" + 
				")\n" +
				"(\n" +
				"sax-costs~sax-costsperti\n" + 
				"(value-String Sym-2)\n" + 
				"(value-String Sym-6)\n" + 
				")\n" +
				")\n" +
				")))"
				, specification.replaceAll("\\s*\\n\\s+", "\n"));
	}

	@Test
	public void testCreateCompeteSpecification()  {
		try{
			PrintWriter pWriter = new PrintWriter(new FileWriter("specification.z3"));
	        for (String line : VerificationSpecificationGenerator.createCompeteSpecification(manager))
	        	pWriter.println(line);
	        pWriter.flush();
	        pWriter.close();
	    } catch(Exception e){
	    	System.out.println("Message: " + e.getMessage());
	        e.printStackTrace();
	    } 
	}

}
