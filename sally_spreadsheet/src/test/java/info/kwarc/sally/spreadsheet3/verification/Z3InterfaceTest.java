package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;

import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class Z3InterfaceTest {
	Z3Interface z3;
	Manager manager;
	ConcreteSpreadsheet spreadsheet;
	
	final Logger logger = LoggerFactory.getLogger(Z3InterfaceTest.class);

	@Before
	public void setUp() throws Exception {
		WinogradData winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
		
		z3 = new Z3Interface();
	}

	@Test
	public void testVerify() {
		List<String> specification = new ArrayList<String>();
		
		List<DataSymbolInformation> dataSym = VerificationDataExtractor.extractDataTypes(manager.getBlockTypes(manager.getAllTopLevelBlocks()), spreadsheet);
		
		// Specification of symbols, axioms and functions
		specification.add( VerificationSpecificationGenerator.getObjectSymbolSpecification(dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllBasicFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllBasicFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.getDataTypeSpecification(manager, dataSym) );
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDeclarations(manager.getOntologyInterface().getAllDomainFunctionObjects(), manager));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionDefinitions( manager.getOntologyInterface().getAllDomainFunctionObjects(), manager, dataSym));
		
		specification.addAll( VerificationSpecificationGenerator.createFunctionSymbolAssertions(manager, dataSym));
		
		/*parseResult(z3.verify(specification, false), "Background Knowledge");
		
		for (AxiomObject axiom : manager.getOntologyInterface().getAxioms())
			parseResult(z3.verify( VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym), false), "Axiom " + axiom.getUri());
		
		for (CPSimilarBlockData cpBlock : VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML()))
			parseResult(z3.verify( VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym), true), "FBBlock for: " + cpBlock.getRelation().getUri());
		*/
		assertEquals(z3.verify(specification, false), VerificationStatus.SAT);
		
		for (AxiomObject axiom : manager.getOntologyInterface().getAxioms())
			assertEquals(z3.verify(VerificationSpecificationGenerator.getAxiom(manager, axiom, dataSym), false), VerificationStatus.SAT);
		
		for (DataSymbolInformation symbol : dataSym)
			assertEquals(z3.verify(VerificationSpecificationGenerator.createSymbolValueAssertion(manager, symbol), false), VerificationStatus.SAT);
		
		for (CPSimilarBlockData cpBlock : VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML()))
			assertEquals(z3.verify(VerificationSpecificationGenerator.getCPSimilarBlockSpec(manager, cpBlock, dataSym), true), VerificationStatus.UNSAT);
	}
	
	private void parseResult(VerificationStatus status, String msg) {
		String text = "Status for " + msg + ": ";
		switch (status) {
		case SAT: 
			logger.info(text + " Valid.");
			break;
		case UNSAT:
			logger.info(text + " Unsat.");
			break;
		case FAILED:
			logger.info(text + " Verification error.");
			break;
		}
	}

}
