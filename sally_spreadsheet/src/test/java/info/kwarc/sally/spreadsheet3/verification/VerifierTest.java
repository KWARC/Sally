package info.kwarc.sally.spreadsheet3.verification;

import static org.junit.Assert.*;

import java.util.List;

import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

public class VerifierTest {
	Manager manager;
	ConcreteSpreadsheet spreadsheet;
	WinogradData winData;
	Verifier verifier;
	
	@Before
	public void setUp() throws Exception {
		winData = new WinogradData();
		manager = winData.getManager();
		spreadsheet = winData.getSpreadsheet();
		
		verifier = new Verifier(manager, spreadsheet);
	}

	@Test
	public void testCheckValue() {
		assertEquals(VerificationStatus.SAT, verifier.checkValue(new CellSpaceInformation("Table1",4,1)) ) ;
		spreadsheet.get(new CellSpaceInformation("Table1",4,1)).setValue("0.0001");		// Value is to low (0.0001 * 1000000 < 100000)
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkValue(new CellSpaceInformation("Table1",4,1)) );
	}

	@Test
	public void testCheckAllValues() {
		assertEquals(VerificationStatus.SAT, verifier.checkAllValues() ) ;
		spreadsheet.get(new CellSpaceInformation("Table1",4,1)).setValue("0.0001");		// Constrains for expenses do not hold any more
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkAllValues() ) ;
	}

	@Test
	public void testCheckCPSimilarBlock() {
		List<CPSimilarBlockData> cpBlocks = VerificationDataExtractor.extractCPSimilarFBs(manager, spreadsheet, manager.getOntologyInterface().getBuilderML());
		for (CPSimilarBlockData block : cpBlocks)
			assertEquals(VerificationStatus.UNSAT, verifier.checkCPSimilarBlock(block) ) ;
	}

	@Test
	public void testCheckFunction() {
		assertEquals(VerificationStatus.SAT, verifier.checkFunction(new CellSpaceInformation("Table1",5,2), winData.getRelationProfit()));
		spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2-C4");
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkFunction(new CellSpaceInformation("Table1",5,2), winData.getRelationProfit()));
	}
	
	@Ignore
	public void testCheckAllFunctions() {
		assertEquals(VerificationStatus.SAT, verifier.checkAllFunctions());
		spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2+C5");
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkAllFunctions());
	}

	@Test
	public void testCheckRelation() {
		/*Relation profitRel = winData.getRelationProfit();
		assertEquals(VerificationStatus.SAT, verifier.checkRelation(profitRel));
		spreadsheet.get(new CellSpaceInformation("Table1",4,2)).setFormula("C2+C4");	// Wrong formula in different relation
		verifier.reinit();
		assertEquals(VerificationStatus.SAT, verifier.checkRelation(profitRel));
		spreadsheet.get(new CellSpaceInformation("Table1",5,2)).setFormula("C2+C5");	// Wrong formula in profit relation
		verifier.reinit();
		assertEquals(VerificationStatus.UNSAT, verifier.checkRelation(profitRel));*/
		
		assertEquals(VerificationStatus.UNSAT, verifier.checkRelation(winData.getRelationTotalCosts()));
	}
	
}
