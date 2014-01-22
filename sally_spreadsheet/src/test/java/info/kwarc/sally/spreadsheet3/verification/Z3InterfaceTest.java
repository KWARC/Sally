package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Manager;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;
import info.kwarc.sally.spreadsheet3.ontology.OntologyException;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Z3InterfaceTest {
	Z3Interface z3;
	Manager manager;
	ModelManager modelManager;
	ConcreteSpreadsheet spreadsheet;
	IOntologyProvider ontology;
	
	final Logger logger = LoggerFactory.getLogger(Z3InterfaceTest.class);

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		modelManager = winData.getModelManager();
		spreadsheet = winData.getSpreadsheet();
		ontology = winData.getManager().getOntology();
		
		z3 = new Z3Interface();
	}

	@Test
	public void testVerify() throws ModelException, OntologyException {
		List<String> specification = new ArrayList<String>();
		
		List<DataSymbolInformation> dataSym = VerificationDataExtractor.extractDataTypes(modelManager.getBlockTypes(modelManager.getAllTopLevelBlocks()), spreadsheet);
		
		// Specification of symbols, axioms and functions
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(ontology.getAllBasicFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( ontology.getAllBasicFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym) );
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(ontology.getAllDomainFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( ontology.getAllDomainFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSym));
		
		/*parseResult(z3.verify(specification, false), "Background Knowledge");
		
		for (AxiomObject axiom : manager.getOntologyInterface().getAxioms())
			parseResult(z3.verify( VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym), false), "Axiom " + axiom.getUri());
		
		for (CPSimilarBlockData cpBlock : VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML()))
			parseResult(z3.verify( VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym), true), "FBBlock for: " + cpBlock.getRelation().getUri());
		*/
		assertEquals(z3.verify(specification, false), VerificationStatusIntern.SAT);
		
		for (AxiomObject axiom : ontology.getAxioms())
			assertEquals(z3.verify(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym), false), VerificationStatusIntern.SAT);
		
		for (DataSymbolInformation symbol : dataSym)
			assertEquals(z3.verify(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol), false), VerificationStatusIntern.SAT);
		
		for (CPSimilarBlockData cpBlock : VerificationDataExtractor.extractCPSimilarFBs(manager))
			assertEquals(z3.verify(VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym), true), VerificationStatusIntern.UNSAT);
	}
	

}
